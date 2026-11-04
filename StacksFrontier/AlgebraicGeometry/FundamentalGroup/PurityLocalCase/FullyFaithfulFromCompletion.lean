module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteFactorization.Basic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleInternalHom
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.FiniteExtensionFromCompletion
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.LocalLefschetz
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Coproduct
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.SchemeTheoreticImage
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.Henselian.Pair.Criteria
public import StacksFrontier.RingTheory.Henselian.Pair.LocalRing
public import StacksFrontier.RingTheory.Henselian.Pair.Operations

/-!
# Fully faithful restriction of finite étale covers, descended from the completion

In the local Lefschetz situation `(A, f)` write `Â` for the `𝔪`-adic completion of `A`, put
`X' = Spec Â`, and let `U'` and `U'₀` be the base changes to `X'` of the punctured spectra `U`
of `A` and `U₀` of `A / fA`. If `A` is henselian — more generally, if `(A, fA)` is a henselian
pair — then full faithfulness of `FÉt_{U'} ⟶ FÉt_{U'₀}` forces full faithfulness of
`FÉt_U ⟶ FÉt_{U₀}`.

Faithfulness comes for free, because `X' ⟶ X` is faithfully flat. For fullness the internal Hom
of finite étale covers turns a morphism of restricted covers into a section over `U₀` of a
finite étale cover `V ⟶ U`, and what has to be produced is an extension of that section over
`U`. Over the completion such an extension is part of the hypothesis; Zariski's main theorem and
the descent of finite covers along the completion turn it into a finite `Y ⟶ X` restricting to
`V` whose base change to `X'` splits off the section as a clopen piece, that is, into an
idempotent of `Γ(Y) ⊗ Â`. The henselian pair hypothesis lifts the corresponding idempotent of
`Γ(Y) / fΓ(Y)` to `Γ(Y)`, and faithfully flat descent identifies the clopen piece of `Y` it cuts
out with the sought section.

## Main results

* `AlgebraicGeometry.LocalLefschetzSituation.fullyFaithful_finiteEtaleRestriction_of_completion`
  — full faithfulness of restriction descends from the completion.

## Implementation notes

Finite étale covers form `AlgebraicGeometry.FiniteEtaleOver` and restriction is
`AlgebraicGeometry.finiteEtaleBaseChange`; full faithfulness is recorded as
`Nonempty (…).FullyFaithful`, the shape used for `FÉt` elsewhere. Both base changes to `X'` are
categorical pullbacks: `U'` is the pullback of `U ⟶ X` along `X' ⟶ X`, and `U'₀` is the pullback
of `U₀ ⟶ U` along `U' ⟶ U`, which is the base change of `U₀` to `X'`.

## References

* [Stacks Project, Tag 0BLI](https://stacks.math.columbia.edu/tag/0BLI)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.LocalLefschetzSituation

/-- The `𝔪`-adic completion of a Noetherian local ring is faithfully flat over it, because `𝔪`
is contained in the Jacobson radical. -/
@[ega "IV 8.11.4" "partial", sga "1 IV 3.2" "special case"]
private lemma completionMap_faithfullyFlat
    (S : LocalLefschetzSituation.{u}) :
    Module.FaithfullyFlat S.A
      (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A) := by
  exact AdicCompletion.faithfullyFlat_of_le_ringJacobson (IsLocalRing.maximalIdeal S.A) (by
    rw [← Ideal.jacobson_bot]
    exact IsLocalRing.maximalIdeal_le_jacobson ⊥)

/-- The morphism `Spec Â ⟶ Spec A` to the `𝔪`-adic completion is flat and surjective, being the
spectrum of a faithfully flat ring map. -/
private lemma completionMap_flat_surjective
    (S : LocalLefschetzSituation.{u}) :
    Flat (Spec.map (CommRingCat.ofHom
        (algebraMap S.A
          (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A)))) ∧
      Surjective (Spec.map (CommRingCat.ofHom
        (algebraMap S.A
          (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A)))) := by
  rw [flat_and_surjective_SpecMap_iff]
  change (algebraMap S.A
    (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A)).FaithfullyFlat
  rw [RingHom.faithfullyFlat_algebraMap_iff]
  exact completionMap_faithfullyFlat S

/-- Faithfulness of restriction of finite étale covers descends from the completion: the square
`U'₀ ⟶ U₀`, `U'₀ ⟶ U'` is cartesian over `U`, so the two routes from `U'₀` to `U` agree, and
`U'₀ ⟶ U₀` is faithfully flat. -/
private lemma finiteEtaleRestriction_faithful_of_completion
    (S : LocalLefschetzSituation.{u})
    (h : let X' := Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A))
      let completionMap : X' ⟶ S.X :=
        Spec.map (CommRingCat.ofHom
          (algebraMap S.A (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A)))
      let U'ToU := pullback.fst S.UOpen.ι completionMap
      let U'₀ToU' := pullback.snd S.U₀ToU U'ToU
      Nonempty (MorphismProperty.Over.pullback
        ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ U'₀ToU').FullyFaithful) :
    (MorphismProperty.Over.pullback
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ S.U₀ToU).Faithful := by
  let X' := Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A))
  let completionMap : X' ⟶ S.X :=
    Spec.map (CommRingCat.ofHom
      (algebraMap S.A (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A)))
  let U'ToU := pullback.fst S.UOpen.ι completionMap
  let U'₀ToU' := pullback.snd S.U₀ToU U'ToU
  let q : pullback S.U₀ToU U'ToU ⟶ S.U₀ :=
    pullback.fst S.U₀ToU U'ToU
  let P : MorphismProperty Scheme.{u} :=
    (@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale
  let F := MorphismProperty.Over.pullback P ⊤ S.U₀ToU
  let G := MorphismProperty.Over.pullback P ⊤ U'ToU
  let H := MorphismProperty.Over.pullback P ⊤ U'₀ToU'
  let Q := MorphismProperty.Over.pullback P ⊤ q
  have hcompletion := completionMap_flat_surjective S
  let : Flat completionMap := hcompletion.1
  let : Surjective completionMap := hcompletion.2
  let : Flat U'ToU := inferInstance
  let : Surjective U'ToU := inferInstance
  let : Flat q := inferInstance
  let : Surjective q := inferInstance
  let : MorphismProperty.IsStableUnderBaseChange P :=
    MorphismProperty.IsStableUnderBaseChange.inf
  let : P.IsStableUnderBaseChangeAlong U'ToU := inferInstance
  let : P.IsStableUnderBaseChangeAlong U'₀ToU' := inferInstance
  let : P.IsStableUnderBaseChangeAlong q := inferInstance
  let : P.IsStableUnderBaseChangeAlong S.U₀ToU := inferInstance
  let : (CategoryTheory.Over.pullback U'ToU).Faithful := inferInstance
  let : (CategoryTheory.Over.pullback q).Faithful := inferInstance
  let : G.Faithful := Functor.Faithful.of_comp_iso
    (MorphismProperty.Over.pullbackCompForgetIso (P := P) (Q := ⊤) U'ToU)
  let : Q.Faithful := Functor.Faithful.of_comp_iso
    (MorphismProperty.Over.pullbackCompForgetIso (P := P) (Q := ⊤) q)
  rcases h with ⟨hH⟩
  have : H.Faithful := hH.faithful
  have hroute : q ≫ S.U₀ToU = U'₀ToU' ≫ U'ToU := pullback.condition
  have : (F ⋙ Q).Faithful := Functor.Faithful.of_iso
    ((MorphismProperty.Over.pullbackComp (P := P) (Q := ⊤) U'₀ToU' U'ToU).symm ≪≫
      (MorphismProperty.Over.pullbackCongr (P := P) (Q := ⊤) hroute).symm ≪≫
      MorphismProperty.Over.pullbackComp (P := P) (Q := ⊤) q S.U₀ToU)
  exact Functor.Faithful.of_comp F Q

/-- A section of an étale morphism is étale. -/
private lemma etale_of_section {X Y : Scheme.{u}} (π : Y ⟶ X) [Etale π]
    (s : X ⟶ Y) (hs : s ≫ π = 𝟙 X) : Etale s := by
  have h : Etale (s ≫ π) := by rw [hs]; infer_instance
  exact MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) s π inferInstance h

/-- A section of an étale morphism is an open immersion: it is étale, hence flat, and split
mono, hence mono. -/
@[ega "IV 17.9.3"]
private lemma isOpenImmersion_of_section {X Y : Scheme.{u}} (π : Y ⟶ X) [Etale π]
    (s : X ⟶ Y) (hs : s ≫ π = 𝟙 X) : IsOpenImmersion s := by
  have : Etale s := etale_of_section π s hs
  have : IsSplitMono s := IsSplitMono.mk' ⟨π, hs⟩
  exact IsOpenImmersion.of_flat_of_mono s

/-- A section of a separated morphism is a closed immersion. -/
private lemma isClosedImmersion_of_section {X Y : Scheme.{u}} (π : Y ⟶ X)
    [IsSeparated π] (s : X ⟶ Y) (hs : s ≫ π = 𝟙 X) : IsClosedImmersion s := by
  have h : IsClosedImmersion (s ≫ π) := by rw [hs]; infer_instance
  exact IsClosedImmersion.of_comp s π

/-- A finite morphism over a quasi-compact open of a quasi-compact quasi-separated scheme
factors as a quasi-compact open immersion followed by a finite morphism. -/
private lemma exists_open_finite_factorization {X U V : Scheme.{u}} (i : U ⟶ X)
    [IsOpenImmersion i] [QuasiCompact i] (p : V ⟶ U) [IsFinite p]
    [CompactSpace X] [QuasiSeparatedSpace X] :
    ∃ (T : Scheme.{u}) (j : V ⟶ T) (π : T ⟶ X),
      IsOpenImmersion j ∧ QuasiCompact j ∧ IsFinite π ∧ j ≫ π = p ≫ i := by
  obtain ⟨T, j, π, hj, hjqc, hπ, h⟩ :=
    Stacks.FiniteFactorization.exists_isOpenImmersion_isFinite_factorization (p ≫ i)
  exact ⟨T, j, π, hj, hjqc, hπ, h.symm⟩

/-- The complement of the image of a clopen section is an open subscheme, and the section
together with the inclusion of that complement exhibits the target as a coproduct. -/
private lemma exists_clopen_section_complement {X Y : Scheme.{u}} (s : X ⟶ Y)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    ∃ W : Y.Opens, IsClosed (W : Set Y) ∧ IsCompl s.opensRange W ∧
      Nonempty (IsColimit (BinaryCofan.mk s W.ι)) := by
  have hsclosed : IsClosed (s.opensRange : Set Y) := by
    change IsClosed (Set.range s.base)
    exact s.isClosedEmbedding.isClosed_range
  let W : Y.Opens := ⟨(s.opensRange : Set Y)ᶜ, hsclosed.isOpen_compl⟩
  have hWclosed : IsClosed (W : Set Y) := by
    change IsClosed ((s.opensRange : Set Y)ᶜ)
    exact s.opensRange.2.isClosed_compl
  have hcompl : IsCompl s.opensRange W := by
    simp only [isCompl_iff, disjoint_iff, codisjoint_iff, ← TopologicalSpace.Opens.coe_inj]
    simp [W]
  exact ⟨W, hWclosed, hcompl, nonempty_isColimit_binaryCofanMk_of_isCompl s W.ι
    (by rwa [Scheme.Opens.opensRange_ι])⟩

/-- Let `p : W ⟶ U` be finite over an open `U ⊆ X` and let it factor through a finite
`π : Z ⟶ X` by an open immersion. Then the induced morphism `W ⟶ Z ×_X U` is a closed
immersion, being both an open immersion and finite. -/
private lemma finite_open_factorization_becomes_closed_over_open
    {X U W Z : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i]
    (p : W ⟶ U) [IsFinite p] (π : Z ⟶ X) [IsFinite π]
    (j : W ⟶ Z) [IsOpenImmersion j] (h : j ≫ π = p ≫ i) :
    IsClosedImmersion (pullback.lift j p h) := by
  let k := pullback.lift j p h
  have hk₁ : k ≫ pullback.fst π i = j := pullback.lift_fst _ _ _
  have hk₂ : k ≫ pullback.snd π i = p := pullback.lift_snd _ _ _
  have hcompOpen : IsOpenImmersion (k ≫ pullback.fst π i) := by
    rw [hk₁]
    infer_instance
  let : IsOpenImmersion (k ≫ pullback.fst π i) := hcompOpen
  have : IsOpenImmersion (pullback.fst π i) := inferInstance
  have hopen : IsOpenImmersion k := IsOpenImmersion.of_comp k (pullback.fst π i)
  let : IsOpenImmersion k := hopen
  have : IsFinite (pullback.snd π i) := by infer_instance
  have : IsFinite (k ≫ pullback.snd π i) := by
    rw [hk₂]
    infer_instance
  have hfinite : IsFinite k := IsFinite.of_comp k (pullback.snd π i)
  exact IsClosedImmersion.iff_isFinite_and_mono k |>.2 ⟨hfinite, inferInstance⟩

/-- In such a factorization the scheme-theoretic image of the open immersion is finite over `X`
and its base change along `U ⟶ X` is `p`. -/
private lemma finite_open_factorization_image_isPullback
    {X U W Z : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i]
    (p : W ⟶ U) [IsFinite p] (π : Z ⟶ X) [IsFinite π]
    (j : W ⟶ Z) [IsOpenImmersion j] [QuasiCompact j]
    (h : j ≫ π = p ≫ i) :
    IsPullback p j.toImage i (j.imageι ≫ π) := by
  let k : W ⟶ pullback π i := pullback.lift j p h
  let q : pullback π i ⟶ Z := pullback.fst π i
  have hk : k ≫ q = j := pullback.lift_fst _ _ _
  have : IsClosedImmersion k :=
    finite_open_factorization_becomes_closed_over_open i p π j h
  have H : IsPullback (𝟙 W) k j q :=
    IsPullback.of_horiz_isIso_mono ⟨by simpa using hk.symm⟩
  have hker : j.ker.comap q = k.ker := by
    rw [← AlgebraicGeometry.ker_pullback_snd_eq_comap q j]
    rw [← Scheme.Hom.ker_comp_of_isIso H.isoPullback.hom]
    congr 1
    exact H.isoPullback_hom_snd
  have Himage : IsPullback k j.toImage q j.imageι :=
    isPullback_of_isClosedImmersion k j.imageι j.toImage q
      (hk.trans j.toImage_imageι.symm) (by simpa using hker)
  simpa only [k, pullback.lift_snd] using Himage.paste_horiz (IsPullback.of_hasPullback π i).flip

/-- A finite morphism over a quasi-compact open of a quasi-compact quasi-separated scheme is the
base change of a finite morphism over the whole scheme. -/
private lemma exists_finite_extension_of_finite_over_open
    {X U W : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i] [QuasiCompact i]
    (p : W ⟶ U) [IsFinite p] [CompactSpace X] [QuasiSeparatedSpace X] :
    ∃ (Z : Scheme.{u}) (π : Z ⟶ X) (j : W ⟶ Z),
      IsFinite π ∧ IsOpenImmersion j ∧ IsPullback p j i π := by
  obtain ⟨Z, j, π, hj, hjqc, hπ, h⟩ := exists_open_finite_factorization i p
  let := hj
  let := hjqc
  let := hπ
  exact ⟨j.image, j.imageι ≫ π, j.toImage, inferInstance, inferInstance,
    finite_open_factorization_image_isPullback i p π j h⟩

/-- If `p` is the base change of `π` along an open immersion `i`, then adjoining the identity of
the base to both exhibits `id ⨿ p` as the base change of `id ⨿ π` along `i`. -/
private lemma isPullback_coprodMap_desc
    {X U W Z : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i]
    (p : W ⟶ U) (π : Z ⟶ X) (j : W ⟶ Z) [IsOpenImmersion j]
    (H : IsPullback p j i π) :
    IsPullback (coprod.desc (𝟙 U) p) (coprod.map i j) i
      (coprod.desc (𝟙 X) π) := by
  have hj : π ⁻¹ᵁ i.opensRange = j.opensRange := by
    simpa using
      (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H ⊤).symm
  apply IsOpenImmersion.isPullback
  · apply coprod.hom_ext <;> simp [H.w]
  · ext z
    obtain ⟨z, rfl⟩ := (coprodMk X Z).surjective z
    have hmap (w : U ⊕ W) :
        coprod.map i j (coprodMk U W w) = coprodMk X Z (Sum.map i j w) := by
      cases w with
      | inl u =>
        simpa only [coprodMk_inl, Sum.map_inl, Scheme.Hom.comp_apply] using
          congrArg (fun f : U ⟶ X ⨿ Z => f u) (coprod.inl_map i j)
      | inr w =>
        simpa only [coprodMk_inr, Sum.map_inr, Scheme.Hom.comp_apply] using
          congrArg (fun f : W ⟶ X ⨿ Z => f w) (coprod.inr_map i j)
    have hrange (z : X ⊕ Z) :
        (∃ w, coprod.map i j w = coprodMk X Z z) ↔
          ∃ w : U ⊕ W, Sum.map i j w = z := by
      constructor
      · rintro ⟨w, hw⟩
        obtain ⟨w, rfl⟩ := (coprodMk U W).surjective w
        exact ⟨w, (coprodMk X Z).injective ((hmap w).symm.trans hw)⟩
      · rintro ⟨w, rfl⟩
        exact ⟨coprodMk U W w, hmap w⟩
    change (coprod.desc (𝟙 X) π) (coprodMk X Z z) ∈ i.opensRange ↔
      ∃ w, coprod.map i j w = coprodMk X Z z
    rw [hrange]
    cases z with
    | inl x =>
      simp only [coprodMk_inl, ← Scheme.Hom.comp_apply, coprod.inl_desc]
      change (∃ u, i u = x) ↔ ∃ w : U ⊕ W, Sum.map i j w = Sum.inl x
      constructor
      · rintro ⟨u, rfl⟩; exact ⟨Sum.inl u, rfl⟩
      · rintro ⟨u | w, h⟩
        · exact ⟨u, Sum.inl.inj h⟩
        · cases h
    | inr z =>
      simp only [coprodMk_inr, ← Scheme.Hom.comp_apply, coprod.inr_desc]
      change z ∈ π ⁻¹ᵁ i.opensRange ↔ ∃ w : U ⊕ W, Sum.map i j w = Sum.inr z
      rw [hj]
      constructor
      · rintro ⟨w, rfl⟩; exact ⟨Sum.inr w, rfl⟩
      · rintro ⟨u | w, h⟩
        · cases h
        · exact ⟨w, Sum.inr.inj h⟩

/-- A finite étale cover of a quasi-compact open `U ⊆ X` carrying a section extends to a finite
morphism `Y ⟶ X` which carries a clopen section of its own, compatibly with the given one: the
cover splits as the section and its complement, and the complement is compactified. -/
private lemma exists_finite_compactification_with_section
    {X U V : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i] [QuasiCompact i]
    (p : V ⟶ U) [IsFinite p] [Etale p] [CompactSpace X] [QuasiSeparatedSpace X]
    (s : U ⟶ V) (hs : s ≫ p = 𝟙 U) :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ X) (j : V ⟶ Y) (t : X ⟶ Y),
      IsFinite π ∧ IsPullback p j i π ∧
      IsOpenImmersion t ∧ IsClosedImmersion t ∧
      t ≫ π = 𝟙 X ∧ s ≫ j = i ≫ t := by
  have : IsOpenImmersion s := isOpenImmersion_of_section p s hs
  have : IsClosedImmersion s := isClosedImmersion_of_section p s hs
  obtain ⟨W, hWclosed, -, ⟨hc⟩⟩ := exists_clopen_section_complement s
  have : IsClosedImmersion W.ι :=
    IsClosedImmersion.of_isPreimmersion W.ι (by simpa using hWclosed)
  obtain ⟨Z, π, j, hπ, hj, H⟩ :=
    exists_finite_extension_of_finite_over_open i (W.ι ≫ p)
  have := hπ
  have := hj
  let e : U ⨿ W.toScheme ≅ V := (coprodIsCoprod U W.toScheme).coconePointUniqueUpToIso hc
  have he₁ : coprod.inl ≫ e.hom = s := by
    exact (coprodIsCoprod U W.toScheme).comp_coconePointUniqueUpToIso_hom hc ⟨.left⟩
  have he₂ : coprod.inr ≫ e.hom = W.ι := by
    exact (coprodIsCoprod U W.toScheme).comp_coconePointUniqueUpToIso_hom hc ⟨.right⟩
  have hep : e.hom ≫ p = coprod.desc (𝟙 U) (W.ι ≫ p) := by
    apply coprod.hom_ext
    · rw [← Category.assoc, he₁, hs, coprod.inl_desc]
    · rw [← Category.assoc, he₂, coprod.inr_desc]
  have hep' : p = e.inv ≫ coprod.desc (𝟙 U) (W.ι ≫ p) := by
    rw [← hep, Iso.inv_hom_id_assoc]
  have Hp : IsPullback p e.inv (𝟙 U) (coprod.desc (𝟙 U) (W.ι ≫ p)) :=
    IsPullback.of_vert_isIso ⟨by simpa using hep'⟩
  have Htotal : IsPullback p (e.inv ≫ coprod.map i j) i (coprod.desc (𝟙 X) π) := by
    simpa only [Category.id_comp] using Hp.paste_vert (isPullback_coprodMap_desc i _ π j H)
  have : IsClosedImmersion (coprod.inl : X ⟶ X ⨿ Z) := by
    apply IsClosedImmersion.of_isPreimmersion
    have hcompl := isCompl_range_inl_inr X Z
    rw [← hcompl.symm.compl_eq]
    exact (coprod.inr : Z ⟶ X ⨿ Z).isOpenEmbedding.isOpen_range.isClosed_compl
  refine ⟨X ⨿ Z, coprod.desc (𝟙 X) π, e.inv ≫ coprod.map i j,
    coprod.inl, inferInstance, Htotal, inferInstance, inferInstance, coprod.inl_desc .., ?_⟩
  rw [← he₁, Category.assoc, Iso.hom_inv_id_assoc, coprod.inl_map]

/-- A section, over the completed punctured spectrum, of the base change of a finite étale cover
of the punctured spectrum of `A` comes from a finite extension `Y ⟶ Spec A` of the cover whose
base change to `Spec Â` carries a clopen section. -/
private lemma exists_finite_model_of_completed_section
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {V : Scheme.{u}} (p : V ⟶ (Stacks.Divisors.puncturedSpectrum A).toScheme)
    [IsFinite p] [Etale p] :
    let c := Spec.map (CommRingCat.ofHom
      (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))
    let q := pullback.fst (Stacks.Divisors.puncturedSpectrum A).ι c
    let i := pullback.snd (Stacks.Divisors.puncturedSpectrum A).ι c
    ∀ (s : pullback (Stacks.Divisors.puncturedSpectrum A).ι c ⟶ pullback p q),
      s ≫ pullback.snd p q = 𝟙 _ →
        ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A))
          (g : V ⟶ Y) (t : Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ⟶
            pullback f c),
          IsFinite f ∧ IsPullback p g (Stacks.Divisors.puncturedSpectrum A).ι f ∧
          IsOpenImmersion t ∧ IsClosedImmersion t ∧
          t ≫ pullback.snd f c = 𝟙 _ ∧
          s ≫ pullback.fst p q ≫ g = i ≫ t ≫ pullback.fst f c := by
  intro c q i s hs
  obtain ⟨Y', f', g', t', hf', HV', ht'open, ht'closed, ht'f', hst'⟩ :=
    exists_finite_compactification_with_section i (pullback.snd p q) s hs
  have := hf'
  have := ht'open
  have := ht'closed
  obtain ⟨Y, f, g, h, hf, HV, HY, hcomp⟩ :=
    exists_finite_extension_of_completion A V p Y' f' g' HV'
  let e : Y' ≅ pullback f c := HY.flip.isoPullback
  have he₁ : e.hom ≫ pullback.fst f c = h := HY.flip.isoPullback_hom_fst
  have he₂ : e.hom ≫ pullback.snd f c = f' := HY.flip.isoPullback_hom_snd
  refine ⟨Y, f, g, t' ≫ e.hom, hf, HV, inferInstance, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, he₂, ht'f']
  · rw [Category.assoc, he₁, ← Category.assoc i, ← hst', Category.assoc,
      ← hcomp]

/-- For a henselian pair `(A, I)` and an integral `A`-algebra `B`, every idempotent of `B / IB`
is the reduction of an idempotent of `B`. -/
private lemma lift_idempotent_of_henselianPair
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (I : Ideal A) (hI : HenselianPair A I)
    (ebar : B ⧸ I.map (algebraMap A B))
    (hebar : IsIdempotentElem ebar) :
    ∃ e : B, IsIdempotentElem e ∧
      Ideal.Quotient.mk (I.map (algebraMap A B)) e = ebar := by
  have hbijAll : ∀ (C : Type u) [CommRing C] [Algebra A C] [Algebra.IsIntegral A C],
      InducesBijectionOnIdempotents (I.map (algebraMap A C)) :=
    ((henselianPair_tfae.{u, u} A I).out 1 4).mp hI
  have hbij : InducesBijectionOnIdempotents (I.map (algebraMap A B)) := hbijAll B
  obtain ⟨⟨e, he⟩, heq⟩ := hbij.2 ⟨ebar, hebar⟩
  exact ⟨e, he, congrArg Subtype.val heq⟩

/-- For a henselian pair `(A, I)` and an integral `A`-algebra `B`, every clopen subset of
`Spec (B / IB)` is the preimage of a clopen subset of `Spec B`. -/
private lemma exists_isClopen_preimage_quotient_of_henselianPair
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (I : Ideal A) (hI : HenselianPair A I)
    (C₀ : Set (PrimeSpectrum (B ⧸ I.map (algebraMap A B)))) (hC₀ : IsClopen C₀) :
    ∃ C : Set (PrimeSpectrum B), IsClopen C ∧
      PrimeSpectrum.comap (Ideal.Quotient.mk (I.map (algebraMap A B))) ⁻¹' C = C₀ := by
  obtain ⟨e₀, he₀, rfl⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen hC₀
  obtain ⟨e, he, heq⟩ := lift_idempotent_of_henselianPair I hI e₀ he₀
  refine ⟨PrimeSpectrum.basicOpen e, PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩, ?_⟩
  ext x
  change (Ideal.Quotient.mk (I.map (algebraMap A B)) e ∉ x.asIdeal) ↔ e₀ ∉ x.asIdeal
  rw [heq]

/-- Two clopen subsets of a space closed over the spectrum of a local ring are equal as soon as
they agree on the closed fibre: a point of their difference specializes into it. -/
private lemma isClopen_eq_of_eq_on_closedFiber
    {T : Type*} [TopologicalSpace T] (R : Type*) [CommRing R] [IsLocalRing R]
    (f : T → PrimeSpectrum R) (hf : IsClosedMap f)
    {C D : Set T} (hC : IsClopen C) (hD : IsClopen D)
    (h : ∀ x, f x = IsLocalRing.closedPoint R → (x ∈ C ↔ x ∈ D)) : C = D := by
  have hle (C D : Set T) (hC : IsClosed C) (hD : IsOpen D)
      (h : ∀ x, f x = IsLocalRing.closedPoint R → x ∈ C → x ∈ D) : C ⊆ D := by
    intro x hx
    by_contra hxD
    have hm := (IsLocalRing.specializes_closedPoint (f x)).mem_closed
      (hf (C \ D) (hC.inter hD.isClosed_compl)) ⟨x, ⟨hx, hxD⟩, rfl⟩
    obtain ⟨y, ⟨hyC, hyD⟩, hy⟩ := hm
    exact hyD (h y hy hyC)
  exact Set.Subset.antisymm (hle C D hC.isClosed hD.isOpen fun x hx => (h x hx).mp)
    (hle D C hD.isClosed hC.isOpen fun x hx => (h x hx).mpr)

/-- The preimage along a flat morphism of the closure of the image of a quasi-compact morphism is
the closure of the image of the base change. -/
private lemma preimage_closure_range_of_flat
    {X Y V : Scheme.{u}} (f : X ⟶ Y) [Flat f] (g : V ⟶ Y) [QuasiCompact g] :
    f ⁻¹' closure (Set.range g) = closure (Set.range (pullback.snd g f)) := by
  have h := congrArg (fun I : X.IdealSheafData => (I.support : Set X))
    (AlgebraicGeometry.ker_pullback_snd_eq_comap f g)
  simpa only [Scheme.Hom.support_ker, Scheme.IdealSheafData.support_comap,
    TopologicalSpace.Closeds.coe_preimage] using h.symm

/-- The image of `Spec (B / J) ⟶ Spec B` is the zero locus of `J`. -/
private lemma range_SpecMap_quotient (B : Type u) [CommRing B] (J : Ideal B) :
    Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) =
      PrimeSpectrum.zeroLocus J := by
  change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J)) = _
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker]

/-- Let `(A, I)` be a henselian pair, `B` an integral `A`-algebra and `T` faithfully flat and
quasi-compact over `Spec B`, universally closed over the spectrum of a local ring. A clopen
subset of `T` which over the zero locus of `IB` is cut out by a subset of `Spec B` is the
preimage of a clopen subset of `Spec B`. -/
private lemma exists_isClopen_preimage_of_henselianPair
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
    (I : Ideal A) (hI : HenselianPair A I)
    {T : Scheme.{u}} (q : T ⟶ Spec (.of B)) [Flat q] [Surjective q] [QuasiCompact q]
    (R : Type u) [CommRing R] [IsLocalRing R]
    (r : T ⟶ Spec (.of R)) [UniversallyClosed r]
    (D : Set T) (hD : IsClopen D) (E : Set (PrimeSpectrum B))
    (hE : q ⁻¹' E = D ∩ q ⁻¹' PrimeSpectrum.zeroLocus (I.map (algebraMap A B)))
    (hclosed : ∀ x, r x = IsLocalRing.closedPoint R →
      q x ∈ PrimeSpectrum.zeroLocus (I.map (algebraMap A B))) :
    ∃ C : Set (PrimeSpectrum B), IsClopen C ∧ q ⁻¹' C = D := by
  let J := I.map (algebraMap A B)
  let p := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  let q₀ := pullback.fst p q
  let v := pullback.snd p q
  have hp : Set.range p = PrimeSpectrum.zeroLocus J := range_SpecMap_quotient B J
  have hrel : q₀ ⁻¹' (p ⁻¹' E) = v ⁻¹' D := by
    ext x
    have hx : p (q₀ x) = q (v x) :=
      congrArg (fun f : pullback p q ⟶ Spec (.of B) => f x) pullback.condition
    have hJ : q (v x) ∈ PrimeSpectrum.zeroLocus J := by
      rw [← hp, ← hx]
      exact ⟨q₀ x, rfl⟩
    change p (q₀ x) ∈ E ↔ v x ∈ D
    rw [hx]
    have hh := Set.ext_iff.mp hE (v x)
    exact hh.trans (and_iff_left hJ)
  have hE₀ : IsClopen (p ⁻¹' E) := by
    have hquot := Flat.isQuotientMap_of_surjective q₀
    have hpre : IsClopen (q₀ ⁻¹' (p ⁻¹' E)) := by
      rw [hrel]
      exact hD.preimage v.continuous
    exact ⟨hquot.isCoinducing.isClosed_preimage.mp hpre.isClosed,
      hquot.isCoinducing.isOpen_preimage.mp hpre.isOpen⟩
  obtain ⟨C, hC, hC₀⟩ := exists_isClopen_preimage_quotient_of_henselianPair I hI
    (p ⁻¹' E) hE₀
  refine ⟨C, hC, isClopen_eq_of_eq_on_closedFiber R r r.isClosedMap
    (hC.preimage q.continuous) hD ?_⟩
  intro x hx
  have hJ := hclosed x hx
  obtain ⟨z, hz⟩ := hp.symm ▸ hJ
  have hCE : q x ∈ C ↔ q x ∈ E := by
    rw [← hz]
    exact Set.ext_iff.mp hC₀ z
  exact hCE.trans ((Set.ext_iff.mp hE x).trans (and_iff_left hJ))

/-- The preimage of the zero locus of `I` under `Spec B ⟶ Spec A` is the zero locus of `IB`. -/
private lemma preimage_zeroLocus_algebraMap
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A) :
    (Spec.map (CommRingCat.ofHom (algebraMap A B))) ⁻¹' PrimeSpectrum.zeroLocus I =
      PrimeSpectrum.zeroLocus (I.map (algebraMap A B)) := by
  ext x
  change I ≤ x.asIdeal.comap (algebraMap A B) ↔ I.map (algebraMap A B) ≤ x.asIdeal
  exact Ideal.map_le_iff_le_comap.symm

/-- The same descent of clopen subsets for a finite morphism `Y ⟶ Spec A` in place of an affine
`Spec B`: `Y` is the spectrum of its global sections, which is a finite `A`-algebra. -/
private lemma exists_isClopen_preimage_of_finite_henselianPair
    (A : Type u) [CommRing A] [IsLocalRing A]
    (I : Ideal A) (hI : HenselianPair A I) (hIm : I ≤ IsLocalRing.maximalIdeal A)
    {Y T : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsFinite f]
    (q : T ⟶ Y) [Flat q] [Surjective q] [QuasiCompact q]
    (R : Type u) [CommRing R] [IsLocalRing R] [Algebra A R]
    [IsLocalHom (algebraMap A R)]
    (r : T ⟶ Spec (.of R)) [UniversallyClosed r]
    (hqr : q ≫ f = r ≫ Spec.map (CommRingCat.ofHom (algebraMap A R)))
    (D : Set T) (hD : IsClopen D) (E : Set Y)
    (hE : q ⁻¹' E = D ∩ (q ≫ f) ⁻¹' PrimeSpectrum.zeroLocus I) :
    ∃ C : Set Y, IsClopen C ∧ q ⁻¹' C = D := by
  have : IsAffine Y := isAffine_of_isAffineHom f
  let B : Type u := Γ(Y, ⊤)
  let e : Y ≅ Spec (.of B) := Y.isoSpec
  let φ : A →+* B := (Spec.preimage (e.inv ≫ f)).hom
  let : Algebra A B := φ.toAlgebra
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap A B)) = e.inv ≫ f :=
    Spec.map_preimage (e.inv ≫ f)
  have : Module.Finite A B := by
    change φ.Finite
    apply (IsFinite.SpecMap_iff (CommRingCat.ofHom φ)).mp
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A B)))
    rw [hφ]
    infer_instance
  let qB := q ≫ e.hom
  have hqB : qB ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = q ≫ f := by
    rw [hφ]
    simp [qB]
  have hJ : qB ⁻¹' PrimeSpectrum.zeroLocus (I.map (algebraMap A B)) =
      (q ≫ f) ⁻¹' PrimeSpectrum.zeroLocus I := by
    rw [← preimage_zeroLocus_algebraMap A B I]
    change (qB ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) ⁻¹' _ = _
    rw [hqB]
    rfl
  have hE' : qB ⁻¹' (e.inv ⁻¹' E) =
      D ∩ qB ⁻¹' PrimeSpectrum.zeroLocus (I.map (algebraMap A B)) := by
    rw [hJ]
    convert hE using 1
    ext x
    change e.inv (e.hom (q x)) ∈ E ↔ q x ∈ E
    rw [← Scheme.Hom.comp_apply, e.hom_inv_id]
    rfl
  have hclosed (x : T) (hx : r x = IsLocalRing.closedPoint R) :
      qB x ∈ PrimeSpectrum.zeroLocus (I.map (algebraMap A B)) := by
    change x ∈ qB ⁻¹' PrimeSpectrum.zeroLocus (I.map (algebraMap A B))
    rw [hJ, hqr]
    change PrimeSpectrum.comap (algebraMap A R) (r x) ∈ PrimeSpectrum.zeroLocus I
    rw [hx, IsLocalRing.comap_closedPoint]
    exact hIm
  obtain ⟨C, hC, hqC⟩ := exists_isClopen_preimage_of_henselianPair I hI qB R r D hD
    (e.inv ⁻¹' E) hE' hclosed
  exact ⟨e.hom ⁻¹' C, hC.preimage e.hom.continuous, hqC⟩

/-- If base change of finite étale covers along `X₀ ⟶ X` is faithful and `X` is nonempty, then
`X₀` is nonempty: otherwise the two coprojections `X ⟶ X ⨿ X`, which differ, would have equal
base changes. -/
private lemma nonempty_of_faithful_finiteEtale_pullback
    {X X₀ : Scheme.{u}} (j : X₀ ⟶ X) [Nonempty X]
    (hF : (MorphismProperty.Over.pullback
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ j).Faithful) :
    Nonempty X₀ := by
  classical
  by_contra h
  have : IsEmpty X₀ := not_nonempty_iff.mp h
  let P : MorphismProperty Scheme.{u} := (@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale
  let F := MorphismProperty.Over.pullback P ⊤ j
  let A : MorphismProperty.Over P ⊤ X :=
    MorphismProperty.Over.mk ⊤ (𝟙 X) ⟨inferInstance, inferInstance⟩
  have : Etale (coprod.desc (𝟙 X) (𝟙 X)) :=
    etale_coprod (𝟙 X) (𝟙 X) inferInstance inferInstance
  let B : MorphismProperty.Over P ⊤ X :=
    MorphismProperty.Over.mk ⊤ (coprod.desc (𝟙 X) (𝟙 X)) ⟨inferInstance, inferInstance⟩
  let a : A ⟶ B := MorphismProperty.Over.homMk coprod.inl (coprod.inl_desc ..)
  let b : A ⟶ B := MorphismProperty.Over.homMk coprod.inr (coprod.inr_desc ..)
  have : IsEmpty (F.obj A).left :=
    ⟨fun x => isEmptyElim ((pullback.snd (𝟙 X) j) x)⟩
  have hab : F.map a = F.map b := by
    apply MorphismProperty.Over.Hom.ext
    exact isInitialOfIsEmpty.hom_ext _ _
  have : F.Faithful := hF
  have he : (coprod.inl : X ⟶ X ⨿ X) = coprod.inr :=
    congrArg (fun f : A ⟶ B => f.left) (F.map_injective hab)
  obtain ⟨x⟩ := ‹Nonempty X›
  exact inl_ne_inr X X x x (congrArg (fun f : X ⟶ X ⨿ X => f x) he)

/-- If base change of finite étale covers along `j : X₀ ⟶ X` is full, then a section over `X₀`
of a finite étale cover of `X` extends to a section over `X` restricting to it. -/
private lemma exists_section_of_full_finiteEtale_pullback
    {X X₀ V : Scheme.{u}} (j : X₀ ⟶ X) (p : V ⟶ X) [IsFinite p] [Etale p]
    (hfull : (MorphismProperty.Over.pullback
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ j).Full)
    (s : X₀ ⟶ V) (hs : s ≫ p = j) :
    ∃ t : X ⟶ V, t ≫ p = 𝟙 X ∧ j ≫ t = s := by
  let P : MorphismProperty Scheme.{u} := (@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale
  let F := MorphismProperty.Over.pullback P ⊤ j
  let A : MorphismProperty.Over P ⊤ X :=
    MorphismProperty.Over.mk ⊤ (𝟙 X) ⟨inferInstance, inferInstance⟩
  let B : MorphismProperty.Over P ⊤ X :=
    MorphismProperty.Over.mk ⊤ p ⟨inferInstance, inferInstance⟩
  let a : pullback (𝟙 X) j ⟶ pullback p j :=
    pullback.lift (pullback.snd (𝟙 X) j ≫ s) (pullback.snd (𝟙 X) j)
      (by rw [Category.assoc, hs])
  let k : F.obj A ⟶ F.obj B := MorphismProperty.Over.homMk a (by
    exact pullback.lift_snd _ _ _)
  have : F.Full := hfull
  obtain ⟨t, ht⟩ := F.map_surjective k
  refine ⟨t.left, MorphismProperty.Over.w t, ?_⟩
  have ht' : pullback.fst (𝟙 X) j ≫ t.left = pullback.snd (𝟙 X) j ≫ s := by
    have hh := congrArg
      (fun g : F.obj A ⟶ F.obj B => g.left ≫ pullback.fst p j) ht
    have h₁ : (F.map t).left ≫ pullback.fst p j
        = pullback.fst (𝟙 X) j ≫ t.left := pullback.lift_fst _ _ _
    have h₂ : k.left ≫ pullback.fst p j
        = pullback.snd (𝟙 X) j ≫ s := pullback.lift_fst _ _ _
    exact h₁.symm.trans (hh.trans h₂)
  let c : X₀ ⟶ pullback (𝟙 X) j := pullback.lift j (𝟙 X₀) (by simp)
  have hcfst : c ≫ pullback.fst (𝟙 X) j = j := pullback.lift_fst _ _ _
  have hcsnd : c ≫ pullback.snd (𝟙 X) j = 𝟙 X₀ := pullback.lift_snd _ _ _
  have e₁ : (c ≫ pullback.fst (𝟙 X) j) ≫ t.left
      = c ≫ pullback.fst (𝟙 X) j ≫ t.left := Category.assoc _ _ _
  have e₂ : (c ≫ pullback.snd (𝟙 X) j) ≫ s
      = c ≫ pullback.snd (𝟙 X) j ≫ s := Category.assoc _ _ _
  have e₃ : c ≫ pullback.fst (𝟙 X) j ≫ t.left
      = c ≫ pullback.snd (𝟙 X) j ≫ s :=
    congrArg (fun q : pullback (𝟙 X) j ⟶ V => c ≫ q) ht'
  have hstart : j ≫ t.left = (c ≫ pullback.fst (𝟙 X) j) ≫ t.left := by
    rw [hcfst]
  have hend : (c ≫ pullback.snd (𝟙 X) j) ≫ s = s := by
    rw [hcsnd, Category.id_comp]
  exact hstart.trans (e₁.trans (e₃.trans (e₂.symm.trans hend)))

/-- Conversely, if every section over `X₀` of a finite étale cover of `X` extends to a section
over `X`, then base change along `j` is full: the internal Hom of two finite étale covers turns
a morphism between their base changes into such a section. -/
@[sga "4 XII 6.5" "(i)"]
private lemma full_finiteEtale_pullback_of_sections
    {X X₀ : Scheme.{u}} (j : X₀ ⟶ X)
    (hsections : ∀ (W : Over X) [IsFinite W.hom] [Etale W.hom]
      (s : X₀ ⟶ W.left), s ≫ W.hom = j →
        ∃ t : X ⟶ W.left, t ≫ W.hom = 𝟙 X ∧ j ≫ t = s) :
    (MorphismProperty.Over.pullback
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ j).Full := by
  let P : MorphismProperty Scheme.{u} := (@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale
  let F := MorphismProperty.Over.pullback P ⊤ j
  refine ⟨?_⟩
  intro Y Z h
  let Yo : Over X := Over.mk Y.hom
  let Zo : Over X := Over.mk Z.hom
  let : IsFinite Yo.hom := Y.prop.1
  let : Etale Yo.hom := Y.prop.2
  let : IsFinite Zo.hom := Z.prop.1
  let : Etale Zo.hom := Z.prop.2
  obtain ⟨W, hWfin, hWet, ⟨e⟩⟩ :=
    Stacks.FundamentalGroup.exists_finiteEtale_internalHom X Yo Zo
  have : IsFinite W.hom := hWfin
  have : Etale W.hom := hWet
  let B : Over X := Over.mk j
  let T : Over X := Over.mk (𝟙 X)
  let i : B ⟶ T := Over.homMk j
  let P := Yo ⨯ B
  let θ : P.left ⟶ pullback Y.hom j :=
    (Over.prodLeftIsoPullback Yo B).hom
  have hθiso : IsIso θ := by
    change IsIso (Over.prodLeftIsoPullback Yo B).hom
    infer_instance
  have hθfst : θ ≫ pullback.fst Y.hom j = (prod.fst (Y := B)).left :=
    Over.prodLeftIsoPullback_hom_fst Yo B
  have hθsnd : θ ≫ pullback.snd Y.hom j = (prod.snd (X := Yo)).left :=
    Over.prodLeftIsoPullback_hom_snd Yo B
  let hl : pullback Y.hom j ⟶ pullback Z.hom j := h.left
  have hh : hl ≫ pullback.snd Z.hom j = pullback.snd Y.hom j :=
    MorphismProperty.Over.w h
  have hcondZ : pullback.fst Z.hom j ≫ Zo.hom = pullback.snd Z.hom j ≫ j :=
    pullback.condition
  have hsndw : (prod.snd (X := Yo) : P ⟶ B).left ≫ j = P.hom :=
    (prod.snd (X := Yo)).w
  have hsplit : hl ≫ pullback.fst Z.hom j ≫ Zo.hom
      = pullback.snd Y.hom j ≫ j := by
    rw [hcondZ]
    rw [show hl ≫ pullback.snd Z.hom j ≫ j
      = (hl ≫ pullback.snd Z.hom j) ≫ j from (Category.assoc _ _ _).symm, hh]
  have hmUw : (θ ≫ hl ≫ pullback.fst Z.hom j) ≫ Zo.hom = P.hom := by
    rw [show (θ ≫ hl ≫ pullback.fst Z.hom j) ≫ Zo.hom
      = θ ≫ hl ≫ pullback.fst Z.hom j ≫ Zo.hom by
        simp only [Category.assoc], hsplit,
      show θ ≫ pullback.snd Y.hom j ≫ j
        = (θ ≫ pullback.snd Y.hom j) ≫ j from (Category.assoc _ _ _).symm, hθsnd]
    exact hsndw
  let mU : P ⟶ Zo := Over.homMk (θ ≫ hl ≫ pullback.fst Z.hom j) hmUw
  let sB : B ⟶ W := (e.app (Opposite.op B)).inv mU
  have hsB : sB.left ≫ W.hom = j := sB.w
  obtain ⟨tW, htW, hUtW⟩ :=
    hsections W sB.left hsB
  let tB : T ⟶ W := Over.homMk tW htW
  let mT : Yo ⨯ T ⟶ Zo := (e.app (Opposite.op T)).hom tB
  let c : Yo ⟶ T := Over.homMk Y.hom
  let η : Yo ⟶ Yo ⨯ T := prod.lift (𝟙 Yo) c
  let g : Yo ⟶ Zo := η ≫ mT
  let k : Y ⟶ Z := MorphismProperty.Over.homMk g.left g.w
  have hi : i ≫ tB = sB := by
    ext1
    exact hUtW
  let mapi : P ⟶ Yo ⨯ T := (prod.functor.obj Yo).map i
  have hm : mapi ≫ mT = mU := by
    have hn := congrArg (fun q => q tB) (e.hom.naturality i.op)
    change (e.app (Opposite.op B)).hom (i ≫ tB) = mapi ≫ mT at hn
    rw [hi] at hn
    have hmU : (e.app (Opposite.op B)).hom sB = mU := by
      simpa only [sB] using (e.app (Opposite.op B)).inv_hom_id_apply mU
    exact hn.symm.trans hmU
  have hci : (prod.fst (Y := B) : P ⟶ Yo) ≫ c =
      (prod.snd (X := Yo) : P ⟶ B) ≫ i := by
    ext1
    calc
      (prod.fst (Y := B)).left ≫ c.left = P.hom := (prod.fst (Y := B)).w
      _ = (prod.snd (X := Yo)).left ≫ i.left := (prod.snd (X := Yo)).w.symm
  have hmapη : mapi = (prod.fst (Y := B) : P ⟶ Yo) ≫ η := by
    change prod.map (𝟙 Yo) i = (prod.fst (Y := B) : P ⟶ Yo) ≫ η
    apply prod.hom_ext
    · simp only [prod.map_fst, Category.comp_id, η, prod.comp_lift, prod.lift_fst]
    · simp only [prod.map_snd, η, prod.comp_lift, prod.lift_snd]
      exact hci.symm
  have hmg : (prod.fst (Y := B) : P ⟶ Yo) ≫ g = mU := by
    change (prod.fst (Y := B) : P ⟶ Yo) ≫ η ≫ mT = mU
    rw [← Category.assoc, ← hmapη]
    exact hm
  have hmgLeft : (prod.fst (Y := B)).left ≫ k.left = mU.left :=
    congrArg (fun q : P ⟶ Zo => q.left) hmg
  have hπ : pullback.fst Y.hom j ≫ k.left = hl ≫ pullback.fst Z.hom j := by
    rw [← cancel_epi θ, ← Category.assoc, hθfst]
    exact hmgLeft
  refine ⟨k, ?_⟩
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · have h₁ : (F.map k).left ≫ pullback.fst Z.hom j
        = pullback.fst Y.hom j ≫ k.left := pullback.lift_fst _ _ _
    exact h₁.trans hπ
  · have h₂ : (F.map k).left ≫ pullback.snd Z.hom j
        = pullback.snd Y.hom j := pullback.lift_snd _ _ _
    exact h₂.trans hh.symm

/-- Precomposition with a surjective morphism does not change the image. -/
private lemma range_comp_of_surjective
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) [Surjective f] (g : Y ⟶ Z) :
    Set.range (f ≫ g) = Set.range g := by
  change Set.range (g ∘ f) = Set.range g
  rw [Set.range_comp, f.surjective.range_eq, Set.image_univ]

/-- The preimage along a flat morphism of the closure of the image of a quasi-compact morphism is
the closure of the image of any cartesian square over it. -/
@[sga "1 VIII 4.1"]
private lemma preimage_closure_range_of_isPullback
    {V' V Y' Y : Scheme.{u}} {a : V' ⟶ V} {b : V' ⟶ Y'}
    {g : V ⟶ Y} {q : Y' ⟶ Y} [Flat q] [QuasiCompact g]
    (H : IsPullback a b g q) :
    q ⁻¹' closure (Set.range g) = closure (Set.range b) := by
  rw [preimage_closure_range_of_flat q g]
  rw [← H.isoPullback_hom_snd, range_comp_of_surjective]

/-- A nonempty punctured spectrum is dense in the spectrum of the local ring, since every point
specializes to the closed point. -/
private lemma closure_range_puncturedSpectrum_ι
    (A : Type u) [CommRing A] [IsLocalRing A]
    [Nonempty (Stacks.Divisors.puncturedSpectrum A).toScheme] :
    closure (Set.range (Stacks.Divisors.puncturedSpectrum A).ι) = Set.univ := by
  rw [Scheme.Opens.range_ι]
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x = IsLocalRing.closedPoint A
  · obtain ⟨y⟩ := ‹Nonempty (Stacks.Divisors.puncturedSpectrum A).toScheme›
    rw [hx]
    exact (IsLocalRing.specializes_closedPoint y.1).mem_closed isClosed_closure
      (subset_closure y.2)
  · exact subset_closure hx

/-- In the local Lefschetz situation with `U₀` nonempty, the closure in `X` of the image of
`U₀` is the zero locus of `fA`. -/
private lemma closure_range_closedFiber_puncturedSpectrum
    (S : LocalLefschetzSituation.{u}) [Nonempty S.U₀] :
    closure (Set.range (S.U₀ToU ≫ S.UOpen.ι)) =
      PrimeSpectrum.zeroLocus S.principalIdeal := by
  have : IsClosedImmersion S.X₀ToX := by
    exact IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (Ideal.Quotient.mk S.principalIdeal)) Ideal.Quotient.mk_surjective
  rw [S.U₀ToU_comp_immersion]
  change closure (Set.range (S.X₀ToX ∘ S.U₀Open.ι)) = _
  rw [Set.range_comp, S.X₀ToX.isClosedEmbedding.closure_image_eq]
  have hd : closure (Set.range S.U₀Open.ι) = Set.univ := by
    have he := S.U₀Open_eq_puncturedSpectrumOpen
    have : Nonempty (Stacks.Divisors.puncturedSpectrum S.quotientRing).toScheme := by
      rw [← he]
      infer_instance
    rw [Scheme.Opens.range_ι, he]
    simpa only [Scheme.Opens.range_ι] using closure_range_puncturedSpectrum_ι S.quotientRing
  rw [hd, Set.image_univ]
  exact range_SpecMap_quotient _ _

/-- Let `Y ⟶ X` acquire an open section after a faithfully flat quasi-compact base change
`X' ⟶ X`, and let the image of that section be the preimage of an open `C ⊆ Y`. Then `C` is an
open subscheme isomorphic to `X`, so it is the image of a section of `Y ⟶ X`. -/
private lemma exists_section_of_isOpen_preimage
    {X X' Y : Scheme.{u}} (c : X' ⟶ X) [Flat c] [Surjective c] [QuasiCompact c]
    (f : Y ⟶ X) (t : X' ⟶ pullback f c)
    [IsOpenImmersion t] (ht : t ≫ pullback.snd f c = 𝟙 X')
    (C : Set Y) (hC : IsOpen C)
    (hpre : (pullback.fst f c) ⁻¹' C = Set.range t) :
    ∃ s : X ⟶ Y, IsOpenImmersion s ∧ s ≫ f = 𝟙 X ∧ Set.range s = C := by
  let O : Y.Opens := ⟨C, hC⟩
  let q := pullback.fst f c
  have hrange : Set.range (t ≫ q) ⊆ Set.range O.ι := by
    rintro y ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change t x ∈ q ⁻¹' C
    rw [hpre]
    exact ⟨x, rfl⟩
  let v := IsOpenImmersion.lift O.ι (t ≫ q) hrange
  have hv : v ≫ O.ι = t ≫ q := IsOpenImmersion.lift_fac ..
  have H : IsPullback v t O.ι q := by
    apply IsOpenImmersion.isPullback
    · exact hv.symm
    · rw [Scheme.Opens.opensRange_ι]
      ext x
      change q x ∈ C ↔ x ∈ Set.range t
      exact Set.ext_iff.mp hpre x
  have H' : IsPullback (𝟙 X') v c (O.ι ≫ f) := by
    simpa only [ht] using H.flip.paste_horiz (IsPullback.of_hasPullback f c).flip
  have : IsIso (O.ι ≫ f) :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := MorphismProperty.isomorphisms Scheme)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) H'
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ (by infer_instance)
  refine ⟨inv (O.ι ≫ f) ≫ O.ι, inferInstance, ?_, ?_⟩
  · simp only [Category.assoc, IsIso.inv_hom_id]
  · rw [range_comp_of_surjective, Scheme.Opens.range_ι]
    rfl

/-- **Stacks Project, Tag 0BLI.** In the local Lefschetz situation assume that `A` is henselian,
or more generally that `(A, fA)` is a henselian pair. If restriction of finite étale covers from
the punctured spectrum of the `𝔪`-adic completion to its closed fibre is fully faithful, then
restriction from `U` to `U₀` is fully faithful. -/
@[stacks 0BLI]
theorem fullyFaithful_finiteEtaleRestriction_of_completion
    (S : LocalLefschetzSituation.{u})
    (hS : HenselianLocalRing S.A ∨ HenselianPair S.A S.principalIdeal)
    (h : let X' := Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A))
      let completionMap : X' ⟶ S.X :=
        Spec.map (CommRingCat.ofHom
          (algebraMap S.A (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A)))
      let U'ToU := pullback.fst S.UOpen.ι completionMap
      let U'₀ToU' := pullback.snd S.U₀ToU U'ToU
      Nonempty (finiteEtaleBaseChange U'₀ToU').FullyFaithful) :
    Nonempty (finiteEtaleBaseChange S.U₀ToU).FullyFaithful := by
    let P : MorphismProperty Scheme.{u} := (@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale
    let F := MorphismProperty.Over.pullback P ⊤ S.U₀ToU
    let : F.Faithful := finiteEtaleRestriction_faithful_of_completion S h
    have hfull : F.Full := by
      apply full_finiteEtale_pullback_of_sections S.U₀ToU
      intro W hWfin hWet s₀ hs₀
      by_cases hU : Nonempty S.U
      · have := hU
        have : Nonempty S.U₀ := nonempty_of_faithful_finiteEtale_pullback S.U₀ToU
          (finiteEtaleRestriction_faithful_of_completion S h)
        have hI : S.principalIdeal ≤ IsLocalRing.maximalIdeal S.A := by
          apply Ideal.span_le.mpr
          simpa using S.f_mem_maximalIdeal
        have hpair : HenselianPair S.A S.principalIdeal := by
          rcases hS with hlocal | hpair
          · have := hlocal
            exact ((henselianPair_iff_of_le hI).mpr
              (henselianPair_maximalIdeal S.A)).1
          · exact hpair
        let c := Spec.map (CommRingCat.ofHom
          (algebraMap S.A (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A)))
        let q := pullback.fst S.UOpen.ι c
        let i := pullback.snd S.UOpen.ι c
        let r := pullback.snd S.U₀ToU q
        let b₀ := pullback.fst S.U₀ToU q
        let s'₀ : pullback S.U₀ToU q ⟶ pullback W.hom q :=
          pullback.lift (b₀ ≫ s₀) r (by
            rw [Category.assoc, hs₀]
            exact pullback.condition)
        have hH : (MorphismProperty.Over.pullback P ⊤ r).Full := (Classical.choice h).full
        obtain ⟨s', hs', hres⟩ := exists_section_of_full_finiteEtale_pullback r
          (pullback.snd W.hom q) hH s'₀ (pullback.lift_snd _ _ _)
        obtain ⟨Y, f, g, t, hf, HV, htopen, htclosed, ht, hcomp⟩ :=
          exists_finite_model_of_completed_section S.A W.hom s' hs'
        have := hf
        have := htopen
        have := htclosed
        have hc := completionMap_flat_surjective S
        have : Flat c := hc.1
        have : Surjective c := hc.2
        have : QuasiCompact c := inferInstance
        let a := pullback.fst f c
        let d := pullback.snd f c
        change t ≫ d = 𝟙 _ at ht
        change s' ≫ pullback.fst W.hom q ≫ g = i ≫ t ≫ a at hcomp
        have : IsNoetherianRing S.quotientRing := by
          dsimp [AlgebraicGeometry.LocalLefschetzSituation.quotientRing]
          infer_instance
        have : TopologicalSpace.NoetherianSpace S.X₀ := by
          change TopologicalSpace.NoetherianSpace (PrimeSpectrum S.quotientRing)
          infer_instance
        have : TopologicalSpace.NoetherianSpace S.U₀ :=
          S.U₀Open.ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
        have hg : g ≫ f = W.hom ≫ S.UOpen.ι := HV.w.symm
        have hb : b₀ ≫ (s₀ ≫ g) = (r ≫ i) ≫ t ≫ a := by
          calc
            b₀ ≫ (s₀ ≫ g) = s'₀ ≫ pullback.fst W.hom q ≫ g := by
              simp only [s'₀, ← Category.assoc, pullback.lift_fst]
            _ = r ≫ s' ≫ pullback.fst W.hom q ≫ g := by rw [← hres, Category.assoc]
            _ = (r ≫ i) ≫ t ≫ a := by rw [hcomp]; simp only [Category.assoc]
        have H₀ : IsPullback b₀ (r ≫ i) (S.U₀ToU ≫ S.UOpen.ι) c :=
          (IsPullback.of_hasPullback S.U₀ToU q).paste_vert
            (IsPullback.of_hasPullback S.UOpen.ι c)
        have HY₀ : IsPullback b₀ ((r ≫ i) ≫ t) (s₀ ≫ g) a := by
          apply IsPullback.of_bot (h₂₁ := a) (v₂₁ := d) (v₂₂ := f) (h₃₁ := c)
          · simpa only [Category.assoc, ht, Category.comp_id, hg,
              reassoc_of% hs₀] using H₀
          · exact hb
          · exact IsPullback.of_hasPullback f c
        have hE : a ⁻¹' closure (Set.range (s₀ ≫ g)) =
            Set.range t ∩ (a ≫ f) ⁻¹' PrimeSpectrum.zeroLocus S.principalIdeal := by
          rw [preimage_closure_range_of_isPullback HY₀]
          change closure (Set.range (t ∘ (r ≫ i))) = _
          rw [Set.range_comp, t.isClosedEmbedding.closure_image_eq]
          rw [← preimage_closure_range_of_isPullback H₀,
            closure_range_closedFiber_puncturedSpectrum S]
          have he : t ≫ a ≫ f = c := by
            rw [pullback.condition, ← Category.assoc, ht, Category.id_comp]
          ext x
          constructor
          · rintro ⟨z, hz, rfl⟩
            refine ⟨⟨z, rfl⟩, ?_⟩
            change (t ≫ a ≫ f) z ∈ PrimeSpectrum.zeroLocus S.principalIdeal
            rw [he]
            exact hz
          · rintro ⟨⟨z, rfl⟩, hz⟩
            refine ⟨z, ?_, rfl⟩
            change (t ≫ a ≫ f) z ∈ PrimeSpectrum.zeroLocus S.principalIdeal at hz
            rwa [he] at hz
        have htclopen : IsClopen (Set.range t) :=
          ⟨t.isClosedEmbedding.isClosed_range, t.isOpenEmbedding.isOpen_range⟩
        obtain ⟨C, hC, hpre⟩ := exists_isClopen_preimage_of_finite_henselianPair
          S.A S.principalIdeal hpair hI f a
          (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A) d
          pullback.condition (Set.range t) htclopen (closure (Set.range (s₀ ≫ g))) hE
        obtain ⟨v, hvopen, hv, hvrange⟩ :=
          exists_section_of_isOpen_preimage c f t ht C hC.isOpen hpre
        have hsrange : Set.range (s₀ ≫ g) ⊆ C := by
          intro y hy
          obtain ⟨x, hx⟩ := a.surjective y
          rw [← hx]
          change x ∈ a ⁻¹' C
          rw [hpre]
          have hxE : x ∈ a ⁻¹' closure (Set.range (s₀ ≫ g)) := by
            change a x ∈ closure (Set.range (s₀ ≫ g))
            rw [hx]
            exact subset_closure hy
          rw [hE] at hxE
          exact hxE.1
        have : IsOpenImmersion v := hvopen
        let v₀ := IsOpenImmersion.lift v (s₀ ≫ g) (by simpa only [hvrange] using hsrange)
        have hv₀ : v₀ ≫ v = s₀ ≫ g := IsOpenImmersion.lift_fac ..
        have hv₀base : v₀ = S.U₀ToU ≫ S.UOpen.ι := by
          calc
            v₀ = (v₀ ≫ v) ≫ f := by rw [Category.assoc, hv, Category.comp_id]
            _ = (s₀ ≫ g) ≫ f := by rw [hv₀]
            _ = S.U₀ToU ≫ S.UOpen.ι := by rw [Category.assoc, hg, ← Category.assoc, hs₀]
        let s := HV.lift (𝟙 S.U) (S.UOpen.ι ≫ v) (by simp [hv])
        have hsp : s ≫ W.hom = 𝟙 S.U := HV.lift_fst _ _ _
        have hsg : s ≫ g = S.UOpen.ι ≫ v := HV.lift_snd _ _ _
        refine ⟨s, hsp, ?_⟩
        apply HV.hom_ext
        · simp only [Category.assoc, hsp, Category.comp_id, hs₀]
        · rw [Category.assoc, hsg, ← Category.assoc, ← hv₀base, hv₀]
      · have : IsEmpty S.U := not_nonempty_iff.mp hU
        have : IsEmpty S.U₀ := ⟨fun x => isEmptyElim (S.U₀ToU x)⟩
        exact ⟨isInitialOfIsEmpty.to W.left, isInitialOfIsEmpty.hom_ext _ _,
          isInitialOfIsEmpty.hom_ext _ _⟩
    let : F.Full := hfull
    exact ⟨Functor.FullyFaithful.ofFullyFaithful F⟩
end AlgebraicGeometry.LocalLefschetzSituation

end

end

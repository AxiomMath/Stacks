module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleExtension
public import StacksFrontier.AlgebraicGeometry.Blowup.DominatedByBlowup
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.SchemeTheoreticImage

/-!
# Extending a section of a proper morphism after an admissible blowup

Let `S` be a quasi-compact and quasi-separated scheme, let `U ⊆ W ⊆ S` be quasi-compact open
subschemes, let `f : X ⟶ W` be proper and let `s : U ⟶ X` be a section of `f` over `U`. Then
there is a `U`-admissible blowup `b : S' ⟶ S` and a morphism `s' : b⁻¹(W) ⟶ X` with
`s' ≫ f = b|_{b⁻¹(W)}` which extends `s`.

The argument is the one of [Stacks, Tag 0CP1]. Replacing `X` by the scheme-theoretic image of
`s` makes the morphism to `W` an isomorphism over `U` ([Stacks, Tag 0CNG]), so it is dominated
by a `U`-admissible blowup of `W` ([Stacks, Tag 081T]); that blowup extends to a
`U`-admissible blowup of `S` ([Stacks, Tag 080M]), and the dominating morphism, read through
the cartesian square of the extension, is the required section over `b⁻¹(W)`.

## Main results

* `AlgebraicGeometry.exists_isAdmissibleBlowup_extending_section` is [Stacks, Tag 0CP1].

## Implementation notes

The smaller open is an open `U` of the scheme `W`, so the admissibility locus in `S` is its
image `W.ι ''ᵁ U`.

That `s'` extends `s` is expressed by a morphism `t : U ⟶ b⁻¹(W)` over `W` with `t ≫ s' = s`.
Such a `t` is unique: a `U`-admissible blowup is an isomorphism over `U`, so a morphism to
`b⁻¹(W)` whose composite with `b|_{b⁻¹(W)}` is the inclusion of `U` is determined by that
composite. The two clauses together therefore say that the restriction of `s'` to the inverse
image of `U`, which that inverse image identifies with `U`, is `s`.

The two results cited by [Stacks, Tag 081T] which this development does not prove —
[Stacks, Tag 080Y] and [Stacks, Tag 081S] — are carried as hypotheses, in exactly the shape
`AlgebraicGeometry.exists_isAdmissibleBlowup_dominating` consumes them, namely
`AlgebraicGeometry.CartierBoundaryReduction` for the first and
`AlgebraicGeometry.StrictTransformOpenImmersion` for the second. The second is about the
scheme-theoretic image of `s` over `W`, which is the morphism the argument feeds to
[Stacks, Tag 081T].

## References

* [Stacks Project, Tag 0CP1](https://stacks.math.columbia.edu/tag/0CP1)
* [Stacks Project, Tag 081T](https://stacks.math.columbia.edu/tag/081T)
* [Stacks Project, Tag 080M](https://stacks.math.columbia.edu/tag/080M)
* [Stacks Project, Tag 0CNG](https://stacks.math.columbia.edu/tag/0CNG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {S X : Scheme.{u}}

/-- **An admissible blowup is an isomorphism over the open it is admissible for.** The centre of
a `V`-admissible blowup is supported away from `V`, and a blowup is an isomorphism over the
complement of the support of its centre. -/
private lemma isIso_morphismRestrict_of_isAdmissibleBlowup {Y Y' : Scheme.{u}} {V : Y.Opens}
    {g : Y' ⟶ Y} (hg : Stacks.Blowup.IsAdmissibleBlowup V g) : IsIso (g ∣_ V) := by
  obtain ⟨I, -, hdisj, e, he⟩ := hg
  have h : IsIso (Stacks.Blowup.blowUpToBase I ∣_ V) :=
    Stacks.Blowup.isIso_blowUpToBase_restrict_of_subset_compl_support_reesData I V
      fun _ hz ↦ Set.disjoint_left.mp hdisj hz
  have h' : IsIso (e.hom ∣_ Stacks.Blowup.blowUpToBase I ⁻¹ᵁ V) := inferInstance
  rw [← he, morphismRestrict_comp]
  exact IsIso.comp_isIso' h' h

/-- **A morphism which is an isomorphism over an open is monic on morphisms through that open.**
If `q` restricts to an isomorphism over `V` and two morphisms `m`, `n` have the same composite
with `q`, which factors through `V`, then `m = n`. -/
private lemma eq_of_comp_eq_of_isIso_morphismRestrict {A Y : Scheme.{u}} (q : A ⟶ Y)
    (V : Y.Opens) [IsIso (q ∣_ V)] {Z : Scheme.{u}} (u : Z ⟶ V.toScheme) (m n : Z ⟶ A)
    (hm : u ≫ V.ι = m ≫ q) (hn : u ≫ V.ι = n ≫ q) : m = n := by
  have hpb := isPullback_morphismRestrict q V
  have heq : hpb.lift u m hm = hpb.lift u n hn := by
    refine (cancel_mono (q ∣_ V)).1 ?_
    rw [hpb.lift_fst, hpb.lift_fst]
  calc m = hpb.lift u m hm ≫ (q ⁻¹ᵁ V).ι := (hpb.lift_snd u m hm).symm
    _ = hpb.lift u n hn ≫ (q ⁻¹ᵁ V).ι := by rw [heq]
    _ = n := hpb.lift_snd u n hn

/-- **Stacks Project, Tag 0CP1.** Let `S` be a quasi-compact and quasi-separated scheme, let
`W ⊆ S` be a quasi-compact open subscheme and let `U ⊆ W` be a quasi-compact open subscheme.
Let `f : X ⟶ W` be proper and let `s : U ⟶ X` satisfy `s ≫ f = U.ι`. Then there is a
`U`-admissible blowup `b : S' ⟶ S` and a morphism `s' : b⁻¹(W) ⟶ X` with `s' ≫ f = b|_{b⁻¹(W)}`
extending `s`, the extension being witnessed by a morphism `t : U ⟶ b⁻¹(W)` over `W`. -/
@[stacks 0CP1 "with Stacks 080Y and 081S as hypotheses, in the shape Stacks 081T consumes them"]
theorem exists_isAdmissibleBlowup_extending_section [CompactSpace S] [QuasiSeparatedSpace S]
    (W : S.Opens) (U : W.toScheme.Opens) (hW : IsCompact (W : Set S))
    (hU : IsCompact (U : Set W.toScheme)) (f : X ⟶ W.toScheme) [IsProper f]
    (s : U.toScheme ⟶ X) (hs : s ≫ f = U.ι)
    (h080Y : CartierBoundaryReduction W.toScheme U)
    (h081S : StrictTransformOpenImmersion (s.imageι ≫ f) U) :
    ∃ (S' : Scheme.{u}) (b : S' ⟶ S),
      Stacks.Blowup.IsAdmissibleBlowup (W.ι ''ᵁ U) b ∧
        ∃ s' : (b ⁻¹ᵁ W).toScheme ⟶ X,
          s' ≫ f = b ∣_ W ∧
            ∃ t : U.toScheme ⟶ (b ⁻¹ᵁ W).toScheme, t ≫ b ∣_ W = U.ι ∧ t ≫ s' = s := by
  classical
  have : QuasiSeparatedSpace W.toScheme := W.ι.isOpenEmbedding.quasiSeparatedSpace
  -- The scheme-theoretic image of `s` is an isomorphism onto `W` above `U`.
  have hqIso : IsIso ((s.imageι ≫ f) ∣_ U) := by
    have hpb : IsIso (pullback.snd (s.imageι ≫ f) U.ι) :=
      isIso_pullback_snd_imageι_comp_of_section f U (hU.isRetrocompact U.2) s hs
    refine (isIso_comp_left_iff (pullbackRestrictIsoRestrict (s.imageι ≫ f) U).hom _).mp ?_
    rw [pullbackRestrictIsoRestrict_hom_morphismRestrict]
    exact hpb
  -- Hence it is dominated by a `U`-admissible blowup of `W`.
  obtain ⟨B, b₀, hb₀, g₀, hg₀⟩ :=
    exists_isAdmissibleBlowup_dominating (s.imageι ≫ f) U h080Y h081S
  -- That blowup extends to a `W.ι ''ᵁ U`-admissible blowup of `S`.
  have hU' : IsCompact ((W.ι ''ᵁ U : S.Opens) : Set S) := hU.image W.ι.continuous
  obtain ⟨S', b, hb, g, hcart⟩ :=
    Stacks.Blowup.exists_admissibleBlowup_isPullback (W.ι ''ᵁ U) W hU' hW b₀
      (by rw [W.ι.preimage_image_eq U]; exact hb₀)
  -- The canonical section of `b₀` over `U`, and its image in the extended blowup.
  have : IsIso (b₀ ∣_ U) := isIso_morphismRestrict_of_isAdmissibleBlowup hb₀
  obtain ⟨uB, huB⟩ : ∃ u : U.toScheme ⟶ B, u ≫ b₀ = U.ι :=
    ⟨inv (b₀ ∣_ U) ≫ (b₀ ⁻¹ᵁ U).ι, by
      rw [Category.assoc, ← morphismRestrict_ι b₀ U, IsIso.inv_hom_id_assoc]⟩
  have hcompat : U.ι ≫ W.ι = (uB ≫ g) ≫ b := by
    rw [Category.assoc, ← hcart.w, ← Category.assoc, huB]
  obtain ⟨t, htB, htW⟩ : ∃ t : U.toScheme ⟶ (b ⁻¹ᵁ W).toScheme,
      t ≫ b ∣_ W = U.ι ∧ t ≫ (b ⁻¹ᵁ W).ι = uB ≫ g :=
    ⟨(isPullback_morphismRestrict b W).lift U.ι (uB ≫ g) hcompat,
      (isPullback_morphismRestrict b W).lift_fst _ _ _,
      (isPullback_morphismRestrict b W).lift_snd _ _ _⟩
  -- Read `b⁻¹(W)` as the blowup of `W`, through the cartesian square of the extension.
  obtain ⟨v, hvb, hvg⟩ : ∃ v : (b ⁻¹ᵁ W).toScheme ⟶ B,
      v ≫ b₀ = b ∣_ W ∧ v ≫ g = (b ⁻¹ᵁ W).ι :=
    ⟨hcart.lift (b ∣_ W) (b ⁻¹ᵁ W).ι (morphismRestrict_ι b W),
      hcart.lift_fst _ _ _, hcart.lift_snd _ _ _⟩
  refine ⟨S', b, hb, v ≫ g₀ ≫ s.imageι, ?_, t, htB, ?_⟩
  · simp only [Category.assoc]
    rw [hg₀]
    exact hvb
  · -- `t` followed by the comparison is the canonical section of `b₀`, …
    have htv : t ≫ v = uB := by
      refine hcart.hom_ext ?_ ?_
      · rw [Category.assoc, hvb, htB, huB]
      · rw [Category.assoc, hvg, htW]
    -- … which the dominating morphism carries to the section into the image of `s`.
    have hmap : uB ≫ g₀ = s.toImage :=
      eq_of_comp_eq_of_isIso_morphismRestrict (s.imageι ≫ f) U (𝟙 _) (uB ≫ g₀) s.toImage
        (by rw [Category.id_comp, Category.assoc, hg₀, huB])
        (by rw [Category.id_comp, ← Category.assoc, Scheme.Hom.toImage_imageι, hs])
    calc t ≫ v ≫ g₀ ≫ s.imageι
        = (t ≫ v) ≫ g₀ ≫ s.imageι := (Category.assoc t v (g₀ ≫ s.imageι)).symm
      _ = (uB ≫ g₀) ≫ s.imageι := by rw [htv, Category.assoc]
      _ = s := by rw [hmap, Scheme.Hom.toImage_imageι]

end AlgebraicGeometry

end

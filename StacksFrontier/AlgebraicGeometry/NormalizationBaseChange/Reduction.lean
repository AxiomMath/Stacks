module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Relative
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Scheme.FibreResidueField
public import StacksFrontier.Topology.Irreducible.GenericPoints
public import StacksCore.Tactic.StacksAttribute

/-!
# Normalization and reduction

Let `X` be a scheme whose quasi-compact opens have finitely many irreducible components. The
normalization morphism of `X` factors canonically through the reduction of `X`, the closed
subscheme cut out by the nilradical, and that factor is the normalization morphism of the
reduction.

## Main definitions

* `AlgebraicGeometry.Scheme.normalizationToReduction` is the canonical factor of the
  normalization morphism through the reduction.
* `AlgebraicGeometry.Scheme.homeomorphNilradicalSubscheme` identifies the underlying space of the
  reduction of `X` with that of `X`.
* `AlgebraicGeometry.Scheme.genericPointResidueSpectrumReductionIso` identifies the coproduct of
  the spectra of the residue fields at the generic points of the reduction with the one of `X`.
* `AlgebraicGeometry.Scheme.toNormalizationScheme` is the morphism from that coproduct to the
  normalization of `X`.
* `AlgebraicGeometry.Scheme.normalizationReductionIso` is the isomorphism of the normalization of
  `X` with the normalization of the reduction of `X`.

## Main results

* `AlgebraicGeometry.Scheme.finite_irreducibleComponents_reduction`: the reduction inherits the
  finiteness of irreducible components of quasi-compact opens, so it can itself be normalized.
* `AlgebraicGeometry.Scheme.normalizationToReduction_subschemeι` is the factorization equation.
* `AlgebraicGeometry.Scheme.existsUnique_iso_normalizationScheme_reduction`: the normalization of
  `X` is the normalization of the reduction of `X`, uniquely isomorphic to it over the reduction
  and compatibly with the morphisms from the generic-point residue spectra. Its two components
  are `AlgebraicGeometry.Scheme.normalizationReductionIso_hom_normalization` and
  `AlgebraicGeometry.Scheme.genericPointResidueSpectrumReductionIso_hom_toNormalizationScheme`.

## Implementation notes

The normalization of `X` is the relative normalization of `X` in the coproduct of the spectra of
the residue fields at its generic points. That coproduct is a coproduct of spectra of fields,
hence reduced, and relative normalization of a reduced scheme is reduced; so the normalization of
`X` is a reduced scheme and the factorization through the reduction is the one supplied by Tag
0356.

The reduction is taken to be `X.nilradical.subscheme`, the closed subscheme of the ideal sheaf
`X.nilradical`; its underlying space is all of `X`, which is what makes the finiteness transfer
below a purely topological statement about a homeomorphism.

That the factor through the reduction is the normalization of the reduction rests on the
coproducts of the spectra of the residue fields at the generic points of `X` and of its reduction
being the same: the closed immersion of the reduction is a homeomorphism, so it matches up the
generic points, and it is surjective on stalks, so it is an isomorphism on residue fields. With
that identification in hand, the statement is the universal property of relative normalization
over an intermediate scheme integral over the target (Tag 035I), applied to the factorization of
the generic-point residue morphism through the reduction.

The comparison of the two coproducts is phrased with the morphisms
`AlgebraicGeometry.Scheme.reductionResidueSpecHom`, whose stated source and target are the
summands indexed as `Limits.Sigma.whiskerEquiv` indexes them, rather than with `Spec.map` of the
residue-field map directly: the two spellings of the point of `X` are definitionally but not
syntactically equal, which is enough to break the motive of a rewrite.

## References

* [Stacks Project, Tag 035O](https://stacks.math.columbia.edu/tag/035O)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology

universe u

namespace AlgebraicGeometry.Scheme

/-! ### Transfer of finiteness of irreducible components along a homeomorphism -/

/-- A homeomorphism carries irreducible components to irreducible components. -/
private theorem image_mem_irreducibleComponents_of_homeomorph {S T : Type*}
    [TopologicalSpace S] [TopologicalSpace T] (e : S ≃ₜ T) {s : Set S}
    (hs : s ∈ irreducibleComponents S) : e '' s ∈ irreducibleComponents T := by
  have h := preimage_mem_irreducibleComponents hs e.symm.isOpenEmbedding
    (by rcases hs.1.nonempty with ⟨x, hx⟩; exact ⟨x, hx, e.symm.surjective x⟩)
  convert h using 1
  ext y
  simp only [Set.mem_image, Set.mem_preimage]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · exact fun hy ↦ ⟨e.symm y, by simpa using hy, by simp⟩

/-- Finiteness of the set of irreducible components transfers along a homeomorphism. -/
private theorem finite_irreducibleComponents_of_homeomorph {S T : Type*}
    [TopologicalSpace S] [TopologicalSpace T] (e : S ≃ₜ T)
    (hT : (irreducibleComponents T).Finite) : (irreducibleComponents S).Finite := by
  have : Finite (irreducibleComponents T) := hT
  exact Finite.of_injective (fun Z : irreducibleComponents S =>
    (⟨e '' Z.1, image_mem_irreducibleComponents_of_homeomorph e Z.2⟩ :
      irreducibleComponents T))
    fun _ _ h ↦ Subtype.ext (Set.image_injective.mpr e.injective (congrArg Subtype.val h))

/-! ### The reduction can be normalized -/

/-- The reduction of `X` is homeomorphic to `X`: the closed immersion of the reduction is a
closed embedding, and it is surjective because the nilradical ideal sheaf is supported
everywhere. -/
noncomputable def homeomorphNilradicalSubscheme (X : Scheme.{u}) :
    X.nilradical.subscheme ≃ₜ X :=
  X.nilradical.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective
    (fun x ↦ Set.mem_range.mp
      (by rw [X.nilradical.range_subschemeι, Scheme.support_nilradical]; trivial))

/-- The reduction of `X` has the same finiteness property for irreducible components of
quasi-compact opens as `X` itself, hence can be normalized whenever `X` can. -/
theorem finite_irreducibleComponents_reduction (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    ∀ U : X.nilradical.subscheme.Opens,
      IsCompact (U : Set X.nilradical.subscheme) → (irreducibleComponents U).Finite := by
  intro U hU
  let eX := X.homeomorphNilradicalSubscheme
  let V : X.Opens := ⟨eX '' (U : Set X.nilradical.subscheme), eX.isOpen_image.mpr U.2⟩
  exact finite_irreducibleComponents_of_homeomorph
    ((eX.image (U : Set X.nilradical.subscheme)).trans (Homeomorph.setCongr rfl))
    (hX V (hU.image eX.continuous))

/-! ### The normalization is reduced -/

/-- The coproduct of the spectra of the residue fields at the generic points is reduced. -/
private theorem isReduced_genericPointResidueSpectrum (X : Scheme.{u}) :
    IsReduced (genericPointResidueSpectrum X) := by
  unfold genericPointResidueSpectrum
  have : ∀ i, IsReduced ((sigmaOpenCover
      (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1)))).X i) := by
    change ∀ η : genericPoints X, IsReduced (Spec (.of (X.residueField η.1)))
    intro η
    infer_instance
  exact IsReduced.of_openCover _ (sigmaOpenCover _)

/-- The normalization of `X` is a reduced scheme: it is the relative normalization of `X` in a
coproduct of spectra of fields. -/
theorem isReduced_normalizationScheme (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    IsReduced (X.normalizationScheme hX) := by
  have := quasiCompactFromGenericPointResidueFields X hX
  have := quasiSeparatedFromGenericPointResidueFields X
  have := isReduced_genericPointResidueSpectrum X
  change IsReduced (fromGenericPointResidueFields X).normalization
  infer_instance

/-! ### The canonical factorization through the reduction -/

/-- **Stacks Project, Tag 035O.** The canonical factor of the normalization morphism of `X`
through the reduction of `X`. -/
@[stacks 035O "canonical factor"]
noncomputable def normalizationToReduction (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    X.normalizationScheme hX ⟶ X.nilradical.subscheme :=
  letI := isReduced_normalizationScheme X hX
  Classical.choose (Scheme.existsUnique_lift_nilradical_subschemeι (X.normalization hX))

/-- **Stacks Project, Tag 035O.** The normalization morphism of `X` is the composite of its
canonical factor through the reduction with the closed immersion of the reduction. -/
@[stacks 035O "factorization"]
theorem normalizationToReduction_subschemeι (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    X.normalizationToReduction hX ≫ X.nilradical.subschemeι = X.normalization hX :=
  let := isReduced_normalizationScheme X hX
  (Classical.choose_spec
    (Scheme.existsUnique_lift_nilradical_subschemeι (X.normalization hX))).1

/-! ### The generic-point residue spectrum of the reduction -/

/-- The homeomorphism of the reduction of `X` with `X` is the underlying map of the closed
immersion of the reduction. Not a `simp` lemma: it would rewrite the homeomorphism away before
`Homeomorph.symm_apply_apply` can fire. -/
theorem homeomorphNilradicalSubscheme_apply (X : Scheme.{u})
    (x : X.nilradical.subscheme) :
    X.homeomorphNilradicalSubscheme x = X.nilradical.subschemeι x := rfl

/-- The closed immersion of the reduction of `X` matches up the generic points of the
irreducible components of the reduction with those of `X`. -/
noncomputable def genericPointsReductionEquiv (X : Scheme.{u}) :
    genericPoints X.nilradical.subscheme ≃ genericPoints X :=
  Equiv.subtypeEquiv X.homeomorphNilradicalSubscheme.toEquiv
    fun x ↦ (X.homeomorphNilradicalSubscheme.mem_genericPoints_iff x).symm

/-- The generic point of `X` matched with a generic point `ζ` of the reduction of `X` is the image
of `ζ` under the closed immersion of the reduction. -/
@[simp]
theorem genericPointsReductionEquiv_val (X : Scheme.{u})
    (ζ : genericPoints X.nilradical.subscheme) :
    (X.genericPointsReductionEquiv ζ).1 = X.nilradical.subschemeι ζ.1 := rfl

/-- The morphism of spectra of residue fields at a generic point of the reduction of `X` and the
matching generic point of `X`, induced by the closed immersion of the reduction. -/
noncomputable def reductionResidueSpecHom (X : Scheme.{u})
    (ζ : genericPoints X.nilradical.subscheme) :
    Spec (.of (X.nilradical.subscheme.residueField ζ.1)) ⟶
      Spec (.of (X.residueField (X.genericPointsReductionEquiv ζ).1)) :=
  Spec.map (X.nilradical.subschemeι.residueFieldMap ζ.1)

/-- The closed immersion of the reduction of `X` is surjective on stalks, hence an isomorphism
on residue fields, so it identifies the two spectra of residue fields. -/
instance isIso_reductionResidueSpecHom (X : Scheme.{u})
    (ζ : genericPoints X.nilradical.subscheme) : IsIso (X.reductionResidueSpecHom ζ) :=
  haveI : IsIso (X.nilradical.subschemeι.residueFieldMap ζ.1) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      ⟨(X.nilradical.subschemeι.residueFieldMap ζ.1).hom.injective,
        surjective_residueFieldMap_of_surjectiveOnStalks X.nilradical.subschemeι ζ.1⟩
  inferInstanceAs (IsIso (Spec.map (X.nilradical.subschemeι.residueFieldMap ζ.1)))

/-- The coproduct of the spectra of the residue fields at the generic points is the same for
`X` and for the reduction of `X`. -/
noncomputable def genericPointResidueSpectrumReductionIso (X : Scheme.{u}) :
    genericPointResidueSpectrum X.nilradical.subscheme ≅ genericPointResidueSpectrum X :=
  Limits.Sigma.whiskerEquiv X.genericPointsReductionEquiv
    fun ζ ↦ (asIso (X.reductionResidueSpecHom ζ)).symm

/-- Under the identification of the generic-point residue spectra of `X` and of its reduction,
the canonical morphism of the reduction is the canonical morphism of `X`. -/
@[reassoc]
theorem genericPointResidueSpectrumReductionIso_hom_fromGenericPointResidueFields
    (X : Scheme.{u}) :
    X.genericPointResidueSpectrumReductionIso.hom ≫ fromGenericPointResidueFields X =
      fromGenericPointResidueFields X.nilradical.subscheme ≫ X.nilradical.subschemeι := by
  unfold genericPointResidueSpectrumReductionIso fromGenericPointResidueFields
    genericPointResidueSpectrum
  refine Limits.Sigma.hom_ext _ _ fun ζ ↦ ?_
  rw [Limits.Sigma.whiskerEquiv_hom, Limits.Sigma.ι_comp_map'_assoc, Iso.symm_inv, asIso_hom,
    Limits.Sigma.ι_comp_desc, Limits.Sigma.ι_comp_desc_assoc]
  exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField X.nilradical.subschemeι ζ.1

/-! ### The normalization of `X` is the normalization of its reduction -/

/-- The canonical dominant morphism from the coproduct of the spectra of the residue fields at
the generic points of `X` to the normalization of `X`. -/
noncomputable abbrev toNormalizationScheme (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    genericPointResidueSpectrum X ⟶ X.normalizationScheme hX :=
  letI := quasiCompactFromGenericPointResidueFields X hX
  letI := quasiSeparatedFromGenericPointResidueFields X
  (fromGenericPointResidueFields X).toNormalization

/-- The canonical morphism from the generic-point residue spectra of `X` factors through the
reduction of `X` as the dominant factor of the normalization followed by the canonical factor of
the normalization morphism through the reduction. -/
theorem toNormalizationScheme_normalizationToReduction_subschemeι (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    (X.toNormalizationScheme hX ≫ X.normalizationToReduction hX) ≫ X.nilradical.subschemeι =
      fromGenericPointResidueFields X := by
  let := quasiCompactFromGenericPointResidueFields X hX
  let := quasiSeparatedFromGenericPointResidueFields X
  rw [Category.assoc, X.normalizationToReduction_subschemeι hX]
  exact (fromGenericPointResidueFields X).toNormalization_fromNormalization

/-- The canonical factor of the normalization morphism through the reduction is the morphism
supplied by the universal property of relative normalization, for the factorization of the
generic-point residue morphism through the reduction. -/
theorem normalizationToReduction_eq_normalizationDesc (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    [QuasiCompact (fromGenericPointResidueFields X)]
    [QuasiSeparated (fromGenericPointResidueFields X)] :
    X.normalizationToReduction hX =
      (fromGenericPointResidueFields X).normalizationDesc
        (X.toNormalizationScheme hX ≫ X.normalizationToReduction hX)
        X.nilradical.subschemeι
        (X.toNormalizationScheme_normalizationToReduction_subschemeι hX).symm :=
  Scheme.Hom.normalization.hom_ext _ _ _ X.nilradical.subschemeι
    ((fromGenericPointResidueFields X).toNormalization_normalizationDesc _ _ _).symm
    (X.normalizationToReduction_subschemeι hX)
    ((fromGenericPointResidueFields X).normalizationDesc_comp _ _ _)

/-- The canonical factor of the normalization morphism of `X` through the reduction of `X` is an
integral morphism. -/
theorem isIntegralHom_normalizationToReduction (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    IsIntegralHom (X.normalizationToReduction hX) := by
  let := quasiCompactFromGenericPointResidueFields X hX
  let := quasiSeparatedFromGenericPointResidueFields X
  rw [X.normalizationToReduction_eq_normalizationDesc hX]
  infer_instance

/-- **Stacks Project, Tag 035O.** The normalization of `X` is the normalization of the reduction
of `X`: the canonical factor of the normalization morphism of `X` through the reduction is
uniquely isomorphic, over the reduction, to the normalization morphism of the reduction,
compatibly with the morphisms from the generic-point residue spectra. -/
@[stacks 035O "an iso over the reduction with the normalization of the reduction"]
theorem existsUnique_iso_normalizationScheme_reduction (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    ∃! e : X.normalizationScheme hX ≅
        X.nilradical.subscheme.normalizationScheme
          (X.finite_irreducibleComponents_reduction hX),
      (X.genericPointResidueSpectrumReductionIso.hom ≫ X.toNormalizationScheme hX) ≫ e.hom =
          X.nilradical.subscheme.toNormalizationScheme
            (X.finite_irreducibleComponents_reduction hX) ∧
        e.hom ≫ X.nilradical.subscheme.normalization
            (X.finite_irreducibleComponents_reduction hX) =
          X.normalizationToReduction hX := by
  let := quasiCompactFromGenericPointResidueFields X hX
  let := quasiSeparatedFromGenericPointResidueFields X
  let := quasiCompactFromGenericPointResidueFields X.nilradical.subscheme
    (X.finite_irreducibleComponents_reduction hX)
  let := quasiSeparatedFromGenericPointResidueFields X.nilradical.subscheme
  let := X.isIntegralHom_normalizationToReduction hX
  have hcomp : X.genericPointResidueSpectrumReductionIso.hom ≫
      (X.toNormalizationScheme hX ≫ X.normalizationToReduction hX) =
      fromGenericPointResidueFields X.nilradical.subscheme := by
    refine (cancel_mono X.nilradical.subschemeι).mp ?_
    rw [Category.assoc, X.toNormalizationScheme_normalizationToReduction_subschemeι hX]
    exact X.genericPointResidueSpectrumReductionIso_hom_fromGenericPointResidueFields
  refine (Scheme.Hom.normalization_universalProperty_iff_existsUnique_iso
    (fromGenericPointResidueFields X.nilradical.subscheme)
    (X.genericPointResidueSpectrumReductionIso.hom ≫ X.toNormalizationScheme hX)
    (X.normalizationToReduction hX) ((Category.assoc _ _ _).trans hcomp)).mp ?_
  intro T j q hq hjq
  obtain ⟨k, hk, hk_unique⟩ :=
    Scheme.Hom.normalizationDesc_universalProperty (fromGenericPointResidueFields X)
      (X.toNormalizationScheme hX ≫ X.normalizationToReduction hX) X.nilradical.subschemeι
      (X.toNormalizationScheme_normalizationToReduction_subschemeι hX).symm
      T (X.genericPointResidueSpectrumReductionIso.inv ≫ j) q hq (by
        rw [Category.assoc, hjq, ← hcomp, ← Category.assoc, Iso.inv_hom_id, Category.id_comp])
  have hiso : ∀ l : X.normalizationScheme hX ⟶ T,
      ((X.genericPointResidueSpectrumReductionIso.hom ≫ X.toNormalizationScheme hX) ≫ l = j) ↔
        (fromGenericPointResidueFields X).toNormalization ≫ l =
          X.genericPointResidueSpectrumReductionIso.inv ≫ j := by
    intro l
    rw [Category.assoc]
    exact (Iso.eq_inv_comp _).symm
  exact ⟨k, ⟨(hiso k).mpr hk.1,
      hk.2.trans (X.normalizationToReduction_eq_normalizationDesc hX).symm⟩,
    fun l hl ↦ hk_unique l ⟨(hiso l).mp hl.1,
      hl.2.trans (X.normalizationToReduction_eq_normalizationDesc hX)⟩⟩

/-- The isomorphism of the normalization of `X` with the normalization of the reduction of `X`
supplied by Tag 035O. -/
noncomputable def normalizationReductionIso (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    X.normalizationScheme hX ≅
      X.nilradical.subscheme.normalizationScheme
        (X.finite_irreducibleComponents_reduction hX) :=
  Classical.choose (X.existsUnique_iso_normalizationScheme_reduction hX)

/-- **Stacks Project, Tag 035O.** The isomorphism of the normalization of `X` with the
normalization of the reduction of `X` is an isomorphism over the reduction: it carries the
normalization morphism of the reduction to the canonical factor of the normalization morphism of
`X` through the reduction. -/
@[stacks 035O "the iso of X^nu with (X_red)^nu is over X_red"]
theorem normalizationReductionIso_hom_normalization (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    (X.normalizationReductionIso hX).hom ≫
        X.nilradical.subscheme.normalization
          (X.finite_irreducibleComponents_reduction hX) =
      X.normalizationToReduction hX :=
  (Classical.choose_spec (X.existsUnique_iso_normalizationScheme_reduction hX)).1.2

/-- The isomorphism of the normalization of `X` with the normalization of the reduction of `X`
is compatible with the morphisms from the generic-point residue spectra. -/
theorem genericPointResidueSpectrumReductionIso_hom_toNormalizationScheme (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    (X.genericPointResidueSpectrumReductionIso.hom ≫ X.toNormalizationScheme hX) ≫
        (X.normalizationReductionIso hX).hom =
      X.nilradical.subscheme.toNormalizationScheme
        (X.finite_irreducibleComponents_reduction hX) :=
  (Classical.choose_spec (X.existsUnique_iso_normalizationScheme_reduction hX)).1.1

end AlgebraicGeometry.Scheme

end

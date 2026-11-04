module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierComplement
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericFibreFreeBlowup0811
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FinitePresentationFromDenseOpen
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.QuasiCompactOpenIdeal

/-!
# Flattening a module by a blowup

Let `S` be a quasi-compact and quasi-separated scheme, let `f : X ⟶ S` be locally of finite
presentation with `X` quasi-compact, let `F` be a quasi-coherent `𝒪_X`-module of finite type and
let `U ⊆ S` be a quasi-compact open over which `F` is of finite presentation and flat. Then there
is a `U`-admissible blowup `S' ⟶ S` such that the strict transform of `F` is an
`𝒪_{X ×_S S'}`-module of finite presentation, flat over `S'`. This is [Stacks, Tag 0815], the
Raynaud–Gruson flattening theorem.

## Main results

* `AlgebraicGeometry.exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_affineCharts`:
  **[Stacks, Tag 0815]**.

## Implementation notes

The proof follows the source. The flatness assertion is the Raynaud–Gruson induction,
`AlgebraicGeometry.hasFlatteningCentre_of_genericFibreFreeBlowup`, fed with the conclusion of
[Stacks, Tag 0811] in the form `AlgebraicGeometry.finitePresentationHasGenericFibreFreeBlowup`.
Finite presentation then comes from [Stacks, Tag 081N] once `U` is scheme-theoretically dense,
and the third paragraph of [Stacks, Tag 080Y] arranges that: the base is first blown up in a
finite type ideal sheaf `J` cutting out `S ∖ U`
(`AlgebraicGeometry.exists_isFiniteType_idealSheafData_support_eq_compl`), the induction is run
on the strict transform over that blowup, and the two centres amalgamate into one centre `K` on
`S` by [Stacks, Tag 080B] (`Stacks.Blowup.exists_centre_of_successive`) and [Stacks, Tag 080I]
(`AlgebraicGeometry.isFlatOver_strictTransformSheaf_of_iterated`). The support of `K` contains
that of `J` and avoids `U`, so it is exactly `S ∖ U`; hence the inverse image of `U` in the
blowup of `S` in `K` is the complement of the exceptional divisor, an effective Cartier divisor
([Stacks, Tag 02OS]), and is therefore scheme-theoretically dense ([Stacks, Tag 07ZU]).

## References

* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 0811](https://stacks.math.columbia.edu/tag/0811)
* [Stacks Project, Tag 081N](https://stacks.math.columbia.edu/tag/081N)
* [Stacks Project, Tag 080Y](https://stacks.math.columbia.edu/tag/080Y)
* [Stacks Project, Tag 080B](https://stacks.math.columbia.edu/tag/080B)
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {S X : Scheme.{u}}

/-- Blowing up a finite type ideal sheaf gives a proper, quasi-separated blowup over which the
strict transform of a finite type module is quasi-coherent and of finite type, over a base change
of `f` that is locally of finite presentation. -/
private theorem isProper_and_strictTransformSheaf_isFiniteType [QuasiSeparatedSpace S]
    (f : X ⟶ S) [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] (J : S.IdealSheafData) (hJ : J.IsFiniteType) :
    IsProper (blowUpToBase J) ∧ QuasiSeparatedSpace (blowUp J) ∧
      (Stacks.StrictTransform.sheaf f (blowUpToBase J) (exceptionalIdeal J) F).IsQuasicoherent ∧
      (Stacks.StrictTransform.sheaf f (blowUpToBase J) (exceptionalIdeal J) F).IsFiniteType ∧
      LocallyOfFinitePresentation (pullback.snd f (blowUpToBase J)) := by
  have := isProper_blowUpToBase_of_fg J hJ
  exact ⟨this, quasiSeparatedSpace_of_quasiSeparated (blowUpToBase J),
    inferInstance, isFiniteType_strictTransformSheaf f J F,
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f (blowUpToBase J)) inferInstance⟩

/-- **A flattening centre cutting out exactly the complement of `U`.** Under the hypotheses of
[Stacks, Tag 0815] there is a finitely presented centre `K` on `S` with support `S ∖ U` along
which the strict transform of `F` is flat over the blowup.

The base is first blown up in a finite type ideal sheaf `J` with support `S ∖ U`; the
Raynaud–Gruson induction flattens the strict transform over that blowup by a centre `I`, and
[Stacks, Tag 080B] amalgamates `J` and `I` into one centre `K` with
`Supp K = Supp J ∪ b(Supp I)`. -/
theorem exists_flatteningCentre_supportSet_eq_compl [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace X] (f : X ⟶ S) [LocallyOfFinitePresentation f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (U : S.Opens) (hU : IsCompact (U : Set S))
    (hFfp : ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj F).IsFinitePresentation)
    (hFflat : IsFlatOver (f ∣_ U).toLRSHom.toShHom
      ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj F)) :
    ∃ K : S.IdealSheafData, FinitePresentation K.subschemeι ∧
      K.supportSet = (U : Set S)ᶜ ∧
      IsFlatOver (pullback.snd f (blowUpToBase K)).toLRSHom.toShHom
        (Stacks.StrictTransform.sheaf f (blowUpToBase K) (exceptionalIdeal K) F) := by
  obtain ⟨J, hJft, hJsupp⟩ := exists_isFiniteType_idealSheafData_support_eq_compl U hU
  have hJfp : FinitePresentation J.subschemeι :=
    (finitePresentation_subschemeι_iff_isFiniteType J).mpr hJft
  have hJdisj : Disjoint (U : Set S) (J.support : Set S) := by
    rw [hJsupp]
    exact disjoint_compl_right
  obtain ⟨_, _, _, _, _⟩ := isProper_and_strictTransformSheaf_isFiniteType f F J hJft
  have _ : CompactSpace (blowUp J) := QuasiCompact.compactSpace_of_compactSpace (blowUpToBase J)
  have _ : CompactSpace (Stacks.StrictTransform.baseChange f (blowUpToBase J)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst f (blowUpToBase J))
  obtain ⟨I, hIfp, hIdisj, hIflat⟩ :=
    hasFlatteningCentre_of_genericFibreFreeBlowup finitePresentationHasGenericFibreFreeBlowup
      (pullback.snd f (blowUpToBase J))
      (Stacks.StrictTransform.sheaf f (blowUpToBase J) (exceptionalIdeal J) F)
      (blowUpToBase J ⁻¹ᵁ U) ((blowUpToBase J).isCompact_preimage hU)
      (isFinitePresentation_strictTransformSheaf_on_admissible_open f J F U hJdisj hFfp)
      (isFlatOver_strictTransformSheaf_on_admissible_open f J F inferInstance U hJdisj hFflat)
  obtain ⟨K, hKfp, hKdisj, hKsupp, ⟨e⟩⟩ :=
    Stacks.Blowup.exists_centre_of_successive secondCentreFactorization U J hJfp hJdisj I hIfp
      hIdisj
  refine ⟨K, hKfp, subset_antisymm (fun x hx hxU ↦ Set.disjoint_left.mp hKdisj hxU hx) ?_,
    isFlatOver_strictTransformSheaf_of_iterated f J K I hKsupp e F hIflat⟩
  rw [hKsupp, ← hJsupp]
  exact Set.subset_union_left

/-- **Stacks Project, Tag 0815.** Let `S` be a quasi-compact and quasi-separated scheme, let
`f : X ⟶ S` be locally of finite presentation with `X` quasi-compact, let `F` be a quasi-coherent
`𝒪_X`-module of finite type and let `U ⊆ S` be a quasi-compact open such that the restriction of
`F` to `f⁻¹(U)` is of finite presentation and flat over `U`. Then there is a centre `I` on `S`,
finitely presented and supported away from `U`, exhibiting the blowup of `S` in `I` as a
`U`-admissible blowup, such that the strict transform of `F` along that blowup is an
`𝒪_{X ×_S S'}`-module of finite presentation and flat over the blowup.

The centre is the one of `AlgebraicGeometry.exists_flatteningCentre_supportSet_eq_compl`, whose
support is `S ∖ U`; so the inverse image of `U` in the blowup is the complement of the exceptional
divisor, hence retrocompact and scheme-theoretically dense, and [Stacks, Tag 081N] gives finite
presentation of the flat strict transform from its finite presentation over that open. -/
@[stacks 0815]
theorem exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_affineCharts
    [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace X] (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (U : S.Opens) (hU : IsCompact (U : Set S))
    (hFfp : ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj F).IsFinitePresentation)
    (hFflat : IsFlatOver (f ∣_ U).toLRSHom.toShHom
      ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj F)) :
    ∃ I : S.IdealSheafData,
      FinitePresentation I.subschemeι ∧
      Disjoint (U : Set S) (I.support : Set S) ∧
      Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase I) ∧
      (Stacks.StrictTransform.sheaf f (blowUpToBase I)
        (exceptionalIdeal I) F).IsFinitePresentation ∧
      IsFlatOver (pullback.snd f (blowUpToBase I)).toLRSHom.toShHom
        (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F) := by
  obtain ⟨K, hKfp, hKsupp, hKflat⟩ :=
    exists_flatteningCentre_supportSet_eq_compl f F U hU hFfp hFflat
  have hKdisj : Disjoint (U : Set S) (K.support : Set S) := by
    change Disjoint _ K.supportSet
    rw [hKsupp]
    exact disjoint_compl_right
  have hKft : K.IsFiniteType := (finitePresentation_subschemeι_iff_isFiniteType K).mp hKfp
  obtain ⟨_, _, _, _, _⟩ := isProper_and_strictTransformSheaf_isFiniteType f F K hKft
  -- The inverse image of `U` is the complement of the exceptional divisor.
  have hUK : (exceptionalIdeal K).support.compl = blowUpToBase K ⁻¹ᵁ U := by
    apply TopologicalSpace.Opens.ext
    have hcomap : ((exceptionalIdeal K).support : Set (blowUp K)) =
        (blowUpToBase K).base ⁻¹' (K.support : Set S) := by
      change ((K.comap (blowUpToBase K)).support : Set (blowUp K)) = _
      rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage]
    change ((exceptionalIdeal K).support : Set (blowUp K))ᶜ = _
    rw [hcomap]
    change ((blowUpToBase K).base ⁻¹' K.supportSet)ᶜ = _
    rw [hKsupp, Set.preimage_compl, compl_compl, Scheme.Hom.coe_preimage]
  have hdense : Scheme.Opens.IsSchemeTheoreticallyDense (blowUpToBase K ⁻¹ᵁ U) :=
    hUK ▸ Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor
      (exceptionalIdeal K) (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal K)
  have hretro : IsRetrocompact ((blowUpToBase K ⁻¹ᵁ U : (blowUp K).Opens) : Set (blowUp K)) :=
    ((blowUpToBase K).isCompact_preimage hU).isRetrocompact (blowUpToBase K ⁻¹ᵁ U).isOpen
  refine ⟨K, hKfp, hKdisj, (Stacks.Blowup.isAdmissibleBlowup_iff U (blowUpToBase K)).mpr
    ⟨K, hKfp, hKdisj, Iso.refl _, Category.id_comp _⟩, ?_, hKflat⟩
  exact
    FinitePresentationFromDenseOpen.isFinitePresentation_of_isFlatOver_of_retrocompact_dense_open
    (pullback.snd f (blowUpToBase K)) _ hKflat (blowUpToBase K ⁻¹ᵁ U) hretro hdense
    (isFinitePresentation_strictTransformSheaf_on_admissible_open f K F U hKdisj hFfp)

end AlgebraicGeometry

end

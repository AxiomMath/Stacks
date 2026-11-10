module

public import StacksFrontier.AlgebraicGeometry.Blowup.DominatedByBlowup
public import StacksFrontier.AlgebraicGeometry.Blowup.SecondCentre
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformIsoOverOpen
public import StacksFrontier.AlgebraicGeometry.Blowup.SuccessiveCentre
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.RegularPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierComplement
public import StacksFrontier.AlgebraicGeometry.Divisors.LocallyPrincipalComplementAffine
public import StacksFrontier.AlgebraicGeometry.Flatness.ExtendingFromOpen.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FiniteTypeStrictTransformFlattening
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.QuasiCompactOpenIdeal
public import StacksFrontier.AlgebraicGeometry.StrictTransform.CompositionScheme

/-!
# A strict transform becomes an open subscheme after a `U`-admissible blowup

Let `f : X ⟶ S` be a separated morphism of finite type with `S` quasi-compact and
quasi-separated, and let `U ⊆ S` be a quasi-compact open over which `f` is an isomorphism. Then
there is a `U`-admissible blowup `S' ⟶ S` along which the strict transform of `X` is an open
subscheme of `S'`.

## Main results

* `AlgebraicGeometry.exists_isAdmissibleBlowup_isOpenImmersion_strictTransform`: there is a
  finitely presented centre avoiding `U` along whose blowup the strict transform of `X` is an
  open subscheme.
* `AlgebraicGeometry.strictTransformOpenImmersion_of_isIso_morphismRestrict`: the same statement
  packaged as `AlgebraicGeometry.StrictTransformOpenImmersion`.

## References

* [Stacks Project, Tag 081S](https://stacks.math.columbia.edu/tag/081S)
* [Stacks Project, Tag 080Y](https://stacks.math.columbia.edu/tag/080Y)
* [Stacks Project, Tag 081R](https://stacks.math.columbia.edu/tag/081R)
* [Stacks Project, Tag 081M](https://stacks.math.columbia.edu/tag/081M)
* [Stacks Project, Tag 080B](https://stacks.math.columbia.edu/tag/080B)
* [Stacks Project, Tag 080I](https://stacks.math.columbia.edu/tag/080I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Let `f : X ⟶ S` be a separated morphism of finite type with `S` quasi-compact and
quasi-separated, and let `U ⊆ S` be a quasi-compact open such that `f` is an isomorphism over
`U`. Then there is a centre `M` on `S`, finitely presented and supported away from `U`, such
that the blowup of `S` in `M` is `U`-admissible and the strict transform of `X` along it is an
open subscheme of that blowup. -/
@[stacks 081S]
theorem exists_isAdmissibleBlowup_isOpenImmersion_strictTransform {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [CompactSpace S] [QuasiSeparatedSpace S] (U : S.Opens) (hU : IsCompact (U : Set S))
    [IsIso (f ∣_ U)] :
    ∃ M : S.IdealSheafData, FinitePresentation M.subschemeι ∧
      Disjoint (U : Set S) (M.support : Set S) ∧
        Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase M) ∧
          IsOpenImmersion (strictTransformToBlowUp f M) := by
  obtain ⟨J, hJft, hJsupp⟩ := exists_isFiniteType_idealSheafData_support_eq_compl U hU
  have hJfp : FinitePresentation J.subschemeι :=
    (finitePresentation_subschemeι_iff_isFiniteType J).mpr hJft
  have hJdisj : Disjoint (U : Set S) (J.support : Set S) := hJsupp ▸ disjoint_compl_right
  have hJproper : IsProper (blowUpToBase J) := isProper_blowUpToBase_of_fg J hJft
  have _ : CompactSpace (blowUp J) := QuasiCompact.compactSpace_of_compactSpace (blowUpToBase J)
  have _ : QuasiSeparatedSpace (blowUp J) :=
    quasiSeparatedSpace_of_quasiSeparated (blowUpToBase J)
  have hU₁ : IsCompact ((blowUpToBase J ⁻¹ᵁ U : (blowUp J).Opens) : Set (blowUp J)) :=
    QuasiCompact.isCompact_preimage (f := blowUpToBase J) (U : Set S) U.2 hU
  have _ : IsSeparated (strictTransformToBlowUp f J) := isSeparated_strictTransformToBlowUp f J
  have _ : LocallyOfFiniteType (strictTransformToBlowUp f J) :=
    locallyOfFiniteType_strictTransformToBlowUp f J
  have _ : QuasiCompact (strictTransformToBlowUp f J) := quasiCompact_strictTransformToBlowUp f J
  have _ : QuasiSeparated (strictTransformToBlowUp f J) :=
    quasiSeparated_strictTransformToBlowUp f J
  have _ : IsIso (strictTransformToBlowUp f J ∣_ (blowUpToBase J ⁻¹ᵁ U)) :=
    isIso_strictTransformToBlowUp_morphismRestrict f J U hJdisj
  obtain ⟨K, hKfp, hKdisj, -, hKflat⟩ :=
    exists_isAdmissibleBlowup_flat_strictTransform_of_locallyOfFiniteType
      (strictTransformToBlowUp f J) (blowUpToBase J ⁻¹ᵁ U) hU₁
  have _ : IsSeparated (strictTransformToBlowUp (strictTransformToBlowUp f J) K) :=
    isSeparated_strictTransformToBlowUp (strictTransformToBlowUp f J) K
  have _ : LocallyOfFiniteType (strictTransformToBlowUp (strictTransformToBlowUp f J) K) :=
    locallyOfFiniteType_strictTransformToBlowUp (strictTransformToBlowUp f J) K
  have _ : Flat (strictTransformToBlowUp (strictTransformToBlowUp f J) K) := hKflat
  have _ : IsIso (strictTransformToBlowUp (strictTransformToBlowUp f J) K ∣_
      (blowUpToBase K ⁻¹ᵁ (blowUpToBase J ⁻¹ᵁ U))) :=
    isIso_strictTransformToBlowUp_morphismRestrict (strictTransformToBlowUp f J) K
      (blowUpToBase J ⁻¹ᵁ U) hKdisj
  have hEcart : Stacks.Divisors.IsEffectiveCartierDivisor
      ((exceptionalIdeal J).comap (blowUpToBase K)) :=
    isPullbackDefined_blowUpToBase (I := K) (exceptionalIdeal J) inferInstance
  have hU₂eq : (blowUpToBase K ⁻¹ᵁ (blowUpToBase J ⁻¹ᵁ U) : (blowUp K).Opens) =
      ((exceptionalIdeal J).comap (blowUpToBase K)).support.compl := by
    apply SetLike.coe_injective
    have hcomap : ∀ {Y Z : Scheme.{u}} (g : Y ⟶ Z) (I : Z.IdealSheafData),
        ((I.comap g).support : Set Y) = g.base ⁻¹' (I.support : Set Z) := fun g I => by
      rw [Scheme.IdealSheafData.support_comap]
      rfl
    simp only [exceptionalIdeal, TopologicalSpace.Closeds.coe_compl, hcomap, hJsupp,
      Set.preimage_compl, compl_compl]
    rfl
  have hU₂dense : Scheme.Opens.IsSchemeTheoreticallyDense
      (blowUpToBase K ⁻¹ᵁ (blowUpToBase J ⁻¹ᵁ U) : (blowUp K).Opens) := by
    rw [hU₂eq]
    exact Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor _ hEcart
  have hU₂retro : IsRetrocompact
      ((blowUpToBase K ⁻¹ᵁ (blowUpToBase J ⁻¹ᵁ U) : (blowUp K).Opens) : Set (blowUp K)) := by
    have _ : IsAffineHom (Scheme.Opens.ι
        ((exceptionalIdeal J).comap (blowUpToBase K)).support.compl) :=
      Stacks.Divisors.isAffineHom_compl_of_isEffectiveCartierDivisor _ hEcart
    rw [hU₂eq]
    exact Stacks.StrictTransform.isRetrocompact_of_quasiCompact_ι _
  have hopen₂ : IsOpenImmersion (strictTransformToBlowUp (strictTransformToBlowUp f J) K) :=
    isOpenImmersion_of_isIso_morphismRestrict _ _ hU₂retro hU₂dense
  obtain ⟨M, hMfp, hMdisj, hMsupp, ⟨e⟩⟩ :=
    Stacks.Blowup.exists_centre_of_successive secondCentreFactorization.{u} U J hJfp hJdisj
      K hKfp hKdisj
  obtain ⟨g, -, hg⟩ := Stacks.StrictTransform.strictTransform_comp_blowUp f J M K hMsupp e
  have hiso : IsIso e.hom.left := by
    change IsIso ((Over.forget S).map e.hom)
    infer_instance
  have hg' : g.hom ≫ strictTransformToBlowUp f M =
      strictTransformToBlowUp (strictTransformToBlowUp f J) K ≫ e.hom.left := by
    simpa only [strictTransformToBlowUp, Category.assoc] using hg
  have h₃ : IsOpenImmersion (g.hom ≫ strictTransformToBlowUp f M) := by
    rw [hg']
    infer_instance
  exact ⟨M, hMfp, hMdisj, (Stacks.Blowup.isAdmissibleBlowup_iff U _).mpr
    ⟨M, hMfp, hMdisj, Iso.refl _, Category.id_comp _⟩,
    (MorphismProperty.cancel_left_of_respectsIso (P := @IsOpenImmersion) g.hom
      (strictTransformToBlowUp f M)).1 h₃⟩

/-- A separated morphism of finite type which is an isomorphism over a quasi-compact open `U` of
a quasi-compact quasi-separated base satisfies `AlgebraicGeometry.StrictTransformOpenImmersion`:
along the blowup in some finitely presented centre avoiding `U`, its strict transform is an
open subscheme of the blowup. -/
@[stacks 081S]
theorem strictTransformOpenImmersion_of_isIso_morphismRestrict {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [CompactSpace S] [QuasiSeparatedSpace S] (U : S.Opens) (hU : IsCompact (U : Set S))
    [IsIso (f ∣_ U)] : StrictTransformOpenImmersion f U := by
  obtain ⟨M, hMfp, hMdisj, -, hMopen⟩ :=
    exists_isAdmissibleBlowup_isOpenImmersion_strictTransform f U hU
  exact ⟨M, hMfp, hMdisj, hMopen⟩

end AlgebraicGeometry

end

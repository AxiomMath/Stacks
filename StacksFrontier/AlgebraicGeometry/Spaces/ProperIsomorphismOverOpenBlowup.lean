module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupStrictTransformSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupCompositeCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessReesChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ComplementChartDiagramCofinal
public import StacksFrontier.AlgebraicGeometry.Spaces.DefiningIdealChartFiniteGeneration
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseOpenImmersionBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeIdealOfQuasiCompactOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningMorphismByBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FlatImageSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformIsoNearClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformOverAdmissibleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroLocusClosedProperSupportUnconditional

/-!
# A proper morphism which is an isomorphism over a dense open becomes one after a blowup

Let `S` be a scheme, let `f : X ⟶ B` be a morphism of algebraic spaces over `S` and let
`U ⊆ B` be an open subspace. Suppose that `B` is quasi-compact and quasi-separated, that `U`
is quasi-compact, that `f` is proper and that `f⁻¹(U) ⟶ U` is an isomorphism. Then there is a
`U`-admissible blowup `B' ⟶ B` such that the strict transform `X'` of `X` maps isomorphically
to `B'`. This is [Stacks, Tag 0GUW].

The argument follows the source. Blow `B` up in a finitely presented closed subspace `Z₀`
whose points are the complement of those of `U` (Stacks 0855); the inverse image `U₁` of `U`
is then the complement of an effective Cartier divisor, hence scheme-theoretically dense
(Stacks 085T and 083S), and the strict transform `X₁` of `X` is proper over the blowup `B₁`
and an isomorphism over `U₁`. Flattening by blowing up (Stacks 087E) gives a `U₁`-admissible
blowup `B₂ ⟶ B₁` over which the strict transform `X₂` of `X₁` is flat and of finite
presentation. The inverse image `U₂` of `U₁` is still scheme-theoretically dense, and
`X₂ ⟶ B₂` is separated, flat, locally of finite type and an isomorphism over the quasi-compact
open `U₂`, so it is an open immersion (Stacks 0879); being proper, it has closed image
containing the dense set of points of `U₂`, so it is an isomorphism. The composite
`B₂ ⟶ B` is the blowup of `B` in a finitely presented centre `Y` (Stacks 0860) whose points
are again the complement of those of `U`, so it is `U`-admissible; and `X₂` is the strict
transform of `X` along it (Stacks 0868).

## Main results

* `AlgebraicGeometry.Space.exists_isBlowupAlong_isIso_strictTransformSpaceToBlowUp_of_isProper`:
  Stacks 0GUW, from flattening by blowing up (Stacks 087E, over its held inputs Stacks 07VR and
  0873) and from the comparison of iterated strict transforms of a space (Stacks 0868,
  part (2)).

## Implementation notes

A `U`-admissible blowup is the blowup in a finitely presented closed subspace disjoint from `U`
(`AlgebraicGeometry.Space.IsAdmissibleBlowup`). The strict transform depends on the centre and
not only on the morphism `B' ⟶ B`, so the conclusion names the centre `Z`: it is of finite
presentation, its points avoid those of `U`, `B' ⟶ B` is the blowup of `B` in `Z`, and the
strict transform with respect to `(B' ⟶ B, Z ×_B B')` maps isomorphically to `B'`.

Quasi-separatedness of `B` is absolute quasi-separatedness, which needs the terminal scheme in
the site. The source's hypothesis that `f⁻¹(U) ⟶ U` is an isomorphism is read on the fibre
product `X ×_B U ⟶ U`, as in Stacks 0879.

## References

* [Stacks Project, Tag 0GUW](https://stacks.math.columbia.edu/tag/0GUW)
* [Stacks Project, Tag 087E](https://stacks.math.columbia.edu/tag/087E)
* [Stacks Project, Tag 0868](https://stacks.math.columbia.edu/tag/0868)
* [Stacks Project, Tag 0879](https://stacks.math.columbia.edu/tag/0879)
* [Stacks Project, Tag 0855](https://stacks.math.columbia.edu/tag/0855)
* [Stacks Project, Tag 0860](https://stacks.math.columbia.edu/tag/0860)
-/

/- The main theorem states Stacks 0GUW relative to `h07VR` and `h0873`, the two inputs of
Stacks 087E, in the shape they have in
`exists_isBlowupAlong_isFlat_isFinitePresentation_strictTransformSpaceToBlowUp`, so it carries
no stacks attribute. The tag 0GUW is attached to the form that assumes neither,
`exists_isBlowupAlong_isIso_strictTransformSpaceToBlowUp_of_isProper_unconditional`. Part (2) of
Stacks 0868 is `exists_strictTransformSpace_comp_iso_unconditional`. All three names live in the
namespace `AlgebraicGeometry.Space`. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0GUW, over Stacks 07VR and 0873 (`h07VR`, `h0873`).** Let
`f : X ⟶ A` be a morphism of algebraic spaces over `S` and let `U ⊆ A` be an open subspace.
Assume that `A` is quasi-compact and quasi-separated, that `U` is quasi-compact, that `f` is
proper and that `f⁻¹(U) ⟶ U` is an isomorphism. Then there is a `U`-admissible blowup
`b : A' ⟶ A`, with centre `Z`, such that the strict transform of `X` maps isomorphically to `A'`.

The two hypotheses are the statements of Stacks 07VR and 0873, the held inputs of flattening by
blowing up, Stacks 087E
(`exists_isBlowupAlong_isFlat_isFinitePresentation_strictTransformSpaceToBlowUp`); the
comparison of the strict transform along a composite of two blowups with the iterated strict
transform is part (2) of Stacks 0868 (`exists_strictTransformSpace_comp_iso_unconditional`). See
the module documentation for the argument. -/
theorem exists_isBlowupAlong_isIso_strictTransformSpaceToBlowUp_of_isProper
    (hZ : B.Contains (⊤_ Scheme.{u})) {A X : AlgebraicSpaces B S hS} (f : X ⟶ A)
    (U : OpenSubspaces B S hS A.1)
    (hAqc : IsQuasiCompactSpace B S hS A.1) (hAqs : IsAbsolutelyQuasiSeparated B S hS hZ A.1)
    (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor)
    (hf : IsProper B S hS f.hom) (hiso : IsIso (pullback.snd f.hom U.1.ι))
    (h07VR : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsFinite B S hS g →
      IsQuasiCompactSpace B S hS Y' →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y' →
      ∃ s : IntegralFiniteSystem B S hS g,
        letI := s.indexPreorder
        ∀ (i j : s.indexType) (h : i ≤ j),
          IsClosedImmersion B S hS (s.diagram.map (homOfLE h).op))
    (h0873 : ∀ {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y),
      IsAlgebraicSpace B S hS X → IsAlgebraicSpace B S hS Y →
      IsFiniteType B S hS f → IsSeparated B S hS f →
      IsQuasiCompactSpace B S hS Y → IsAbsolutelyQuasiSeparated B S hS hZ Y →
      ∃ (X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f' : X' ⟶ Y) (i : X ⟶ X'),
        IsAlgebraicSpace B S hS X' ∧ IsSeparated B S hS f' ∧
          IsFinitePresentation B S hS f' ∧ IsClosedImmersion B S hS i ∧ i ≫ f' = f) :
    ∃ (A' : AlgebraicSpaces B S hS) (b : A' ⟶ A) (Z : ClosedSubspaces B S hS A.1),
      IsFinitePresentation B S hS Z.1.ι ∧
        Disjoint (subspacePointSet B S hS A.1 U.1) (subspacePointSet B S hS A.1 Z.1) ∧
          IsBlowupAlong B S hS Z b ∧
            IsIso (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)).hom := by
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) := hasSheafify_bigFppfOver B S hS
  have hUι : IsQuasiCompact B S hS U.1.ι :=
    (isQuasiCompact_iff_isQuasiCompactSpace_openSubspace B S hS hZ A hAqc hAqs U).2 hUqc
  -- Blow up a finitely presented closed subspace with complement `U`.
  obtain ⟨Z₀, hZ₀fp, hZ₀pts⟩ : ∃ Z : ClosedSubspaces B S hS A.1,
      IsFinitePresentation B S hS Z.1.ι ∧
        subspacePointSet B S hS A.1 Z.1 = (subspacePointSet B S hS A.1 U.1)ᶜ := by
    obtain ⟨I, ⟨hIqc, hIft⟩, hIzero⟩ :=
      hasFiniteTypeQuasicoherentIdealZeroLocus_of_isQuasiCompactSpace B S hS hZ A hAqc hAqs U.2
        hUqc
    obtain ⟨Z, hZI⟩ := exists_definingIdealSheaf_eq_of_isCartesianOnAffineCharts B S hS A I
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS A.1 A.2 _ hIqc)
    refine ⟨Z, (isFinitePresentation_iff_isFiniteTypeOnSite_kernelIdealSheaf B S hS
      (ObjectProperty.homMk Z.1.ι : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ A)
      Z.2.2).2 ?_, ?_⟩
    · rw [kernelIdealSheaf_eq_definingIdealSheaf, hZI]
      exact hIft
    · rw [subspacePointSet, range_pointsMap_ι_eq_idealZeroLocus B S hS A Z, hZI, ← hIzero]
  have hUZ₀ : Disjoint (subspacePointSet B S hS A.1 U.1) (subspacePointSet B S hS A.1 Z₀.1) := by
    rw [hZ₀pts]
    exact disjoint_compl_right
  obtain ⟨A₁, b₁, hb₁⟩ := exists_isBlowupAlong_of_isFinitePresentation Z₀ hZ₀fp
  have hb₁p : IsProper B S hS b₁.hom :=
    isProper_of_isBlowupAlong_of_isFinitePresentation B S hS Z₀ b₁ hZ₀fp hb₁
  have _ : IsIso (pullback.snd (𝟙 A.1) b₁.hom) := inferInstance
  have hA₁qc : IsQuasiCompactSpace B S hS A₁.1 :=
    (hb₁p.isFiniteType.2 A.1 A.2 hAqc (𝟙 A.1)).of_iso B S hS
      (asIso (pullback.snd (𝟙 A.1) b₁.hom))
  have hA₁qs : IsAbsolutelyQuasiSeparated B S hS hZ A₁.1 :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ A₁.2 hAqs
      (isQuasiSeparated_of_isSeparated B S hS hb₁p.isSeparated)
  let U₁ : OpenSubspaces B S hS A₁.1 :=
    ⟨U.1.preimage b₁.hom, isOpenSubspace_preimage B S hS b₁.hom U.1 A.2 A₁.2 U.2⟩
  have hU₁ι : IsQuasiCompact B S hS U₁.1.ι :=
    isQuasiCompact_of_isPullback B S hS (Subfunctor.isPullback_preimage b₁.hom U.1) hUι
  have hU₁dense : IsSchemeTheoreticallyDense B S hS U₁.1 :=
    isSchemeTheoreticallyDense_preimage_of_isBlowupAlong U Z₀ hb₁ hZ₀pts
  have hU₁qc : IsQuasiCompactSpace B S hS U₁.1.toFunctor :=
    (isQuasiCompact_iff_isQuasiCompactSpace_openSubspace B S hS hZ A₁ hA₁qc hA₁qs U₁).1 hU₁ι
  -- The strict transform `X₁ ⟶ A₁`: proper, and an isomorphism over `U₁`.
  -- The strict transform of a proper morphism is proper: a closed immersion followed by a base
  -- change of the proper morphism.
  have hstp : ∀ {A₀ X₀ A₀' : AlgebraicSpaces B S hS} (f₀ : X₀ ⟶ A₀) (b₀ : A₀' ⟶ A₀)
      (E : Subfunctor A₀'.1), IsProper B S hS f₀.hom →
        IsProper B S hS (strictTransformSpaceToBlowUp B S hS f₀ b₀ E).hom :=
    fun {_ _ A₀'} f₀ b₀ E hf₀ => isProper_comp B S hS (strictTransformSpace B S hS f₀ b₀ E).2
      (strictTransformPullback B S hS f₀ b₀).2 A₀'.2 _ _
      (isProper_of_isClosedImmersion B S hS (strictTransformSpace B S hS f₀ b₀ E).2
        (strictTransformPullback B S hS f₀ b₀).2 _ (strictTransform B S hS f₀ b₀ E).2.2)
      ((isProper_isStableUnderBaseChange B S hS).of_isPullback
        (AlgebraicSpaces.isPullback_fiberProduct B S hS f₀ b₀) hf₀)
  set f₁ := strictTransformSpaceToBlowUp B S hS f b₁ (Z₀.1.preimage b₁.hom) with hf₁def
  have hf₁ : IsProper B S hS f₁.hom := hstp f b₁ _ hf
  have hf₁iso : IsIso (pullback.snd f₁.hom U₁.1.ι) :=
    isIso_pullbackSnd_strictTransformSpaceToBlowUp f b₁ Z₀ hb₁ U hUZ₀ hiso
  -- Flattening by blowing up.
  obtain ⟨A₂, b₂, Z₁, hZ₁fp, hU₁Z₁, hb₂, hflat₂, hfp₂⟩ :=
    exists_isBlowupAlong_isFlat_isFinitePresentation_strictTransformSpaceToBlowUp hZ h07VR
      h0873 f₁ U₁ hA₁qc hA₁qs hU₁qc hf₁.isFiniteType
      (isQuasiSeparated_of_isSeparated B S hS hf₁.isSeparated)
      (isFlat_of_isIso _ U₁.2.1)
      (isLocallyOfFinitePresentation_of_isOpenImmersion B S hS (isOpenImmersion_of_isIso B S hS _))
  -- The composite blowup, whose centre has complement `U`.
  obtain ⟨Y, hYfp, hYcomp, hYb⟩ := exists_isCompositeCentre_isBlowupAlong hb₁ hZ₀fp hb₂ hZ₁fp
    (hasSecondCentre hZ hAqc hAqs hZ₀fp hb₁)
  have hYpts : subspacePointSet B S hS A.1 Y.1 = (subspacePointSet B S hS A.1 U.1)ᶜ := by
    have hY : subspacePointSet B S hS A.1 Y.1 = subspacePointSet B S hS A.1 Z₀.1 ∪
        pointsMap B S hS A₁.1 b₁.hom '' subspacePointSet B S hS A₁.1 Z₁.1 := hYcomp
    rw [hY, Set.union_eq_left.2, hZ₀pts]
    rintro _ ⟨w, hw, rfl⟩
    rw [hZ₀pts]
    intro hu
    have hwU : w ∈ subspacePointSet B S hS A₁.1 U₁.1 := by
      rw [subspacePointSet_preimage, Set.mem_preimage]
      exact hu
    exact Set.disjoint_left.1 hU₁Z₁ hwU hw
  have hUY : Disjoint (subspacePointSet B S hS A.1 U.1) (subspacePointSet B S hS A.1 Y.1) := by
    rw [hYpts]
    exact disjoint_compl_right
  -- The second strict transform `X₂ ⟶ A₂` is an isomorphism.
  set f₂ := strictTransformSpaceToBlowUp B S hS f₁ b₂ (Z₁.1.preimage b₂.hom) with hf₂def
  let U₂ : OpenSubspaces B S hS A₂.1 :=
    ⟨U₁.1.preimage b₂.hom, isOpenSubspace_preimage B S hS b₂.hom U₁.1 A₁.2 A₂.2 U₁.2⟩
  have hf₂ : IsProper B S hS f₂.hom := hstp f₁ b₂ _ hf₁
  have hf₂iso : IsIso (pullback.snd f₂.hom U₂.1.ι) :=
    isIso_pullbackSnd_strictTransformSpaceToBlowUp f₁ b₂ Z₁ hb₂ U₁ hU₁Z₁ hf₁iso
  have hU₂dense : IsSchemeTheoreticallyDense B S hS U₂.1 :=
    isSchemeTheoreticallyDense_preimage_of_isBlowupAlong_of_isSchemeTheoreticallyDense b₂ Z₁ hb₂
      U₁.1 hU₁dense
  have hf₂open : IsOpenImmersion B S hS f₂.hom :=
    isOpenImmersion_strictTransformSpaceToBlowUp f₁ b₂ Z₁ hb₂ U₁ hU₁Z₁ hU₁ι hU₁dense
      hf₁.isSeparated hf₁iso hflat₂ hf₂.isFiniteType.1
  have hsub : subspacePointSet B S hS A₂.1 U₂.1 ⊆ Set.range (pointsMap B S hS _ f₂.hom) := by
    rintro _ ⟨u, rfl⟩
    obtain ⟨v, hv⟩ := isSurjective_of_isIso B S hS (pullback.snd f₂.hom U₂.1.ι) u
    refine ⟨pointsMap B S hS _ (pullback.fst f₂.hom U₂.1.ι) v, ?_⟩
    rw [← pointsMap_comp_apply, pullback.condition, pointsMap_comp_apply, hv]
  have hdense : DenseRange (pointsMap B S hS _ f₂.hom) :=
    Dense.mono hsub
      (dense_subspacePointSet_of_isSchemeTheoreticallyDense B S hS (X := A₂) U₂.1 hU₂dense)
  have hf₂iso₂ : IsIso f₂.hom :=
    isIso_of_isOpenImmersion_of_denseRange_of_universallyClosed B S hS
      (strictTransformSpace B S hS f₁ b₂ (Z₁.1.preimage b₂.hom)).2 A₂.2 A₂.2 f₂.hom hf₂open
      (𝟙 A₂.1) (isSeparated_of_isIso B S hS (𝟙 A₂.1))
      (by rw [Category.comp_id]; exact hf₂.universallyClosed) hdense
  -- The strict transform along the composite is the second strict transform.
  obtain ⟨k, j, -, hk, hj⟩ :=
    exists_strictTransformSpace_comp_iso_unconditional B S hS f b₁ b₂ Z₀ Z₁ Y hb₁ hb₂ hYcomp hYb
  refine ⟨A₂, b₂ ≫ b₁, Y, hYfp, hUY, hYb, ?_⟩
  have hcomp : j.hom ≫ strictTransformSpaceToBlowUp B S hS f (b₂ ≫ b₁)
      (Y.1.preimage (b₂ ≫ b₁).hom) = f₂ := by
    change j.hom ≫ strictTransformSpaceι B S hS f (b₂ ≫ b₁) (Y.1.preimage (b₂ ≫ b₁).hom) ≫
        strictTransformPullbackToBlowUp B S hS f (b₂ ≫ b₁) =
      strictTransformSpaceι B S hS f₁ b₂ (Z₁.1.preimage b₂.hom) ≫
        strictTransformPullbackToBlowUp B S hS f₁ b₂
    rw [reassoc_of% hj, hk]
  have heq : strictTransformSpaceToBlowUp B S hS f (b₂ ≫ b₁) (Y.1.preimage (b₂ ≫ b₁).hom) =
      j.inv ≫ f₂ := by
    rw [← hcomp, Iso.inv_hom_id_assoc]
  rw [heq]
  have hjinv : IsIso j.inv.hom :=
    ⟨⟨j.hom.hom, by simp, by simp⟩⟩
  change IsIso (j.inv.hom ≫ f₂.hom)
  infer_instance

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningMorphismByBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperIsomorphismOverOpenBlowup

/-!
# A finite type separated modification becomes an open immersion after an admissible blowup

Let `f : X ⟶ A` be a morphism of algebraic spaces and let `U ⊆ A` be an open subspace.  Assume
that `A` is quasi-compact and quasi-separated, that `U` is quasi-compact, that `f` is of finite
type and separated, and that `f⁻¹(U) ⟶ U` is an isomorphism.  Then there is a `U`-admissible
blowup `A' ⟶ A` such that `U` is scheme-theoretically dense in `A'` and the strict transform
of `X` maps isomorphically to an open subspace of `A'`.  This is [Stacks, Tag 087F] with the
hypothesis that `f` be separated added: as published, without it, the statement is false.

**The counterexample.**  Let `k` be a field, `A = 𝐀¹_k`, `U = 𝐀¹_k ∖ {0}`, and let `X` be the
affine line with doubled origin, with its morphism to `𝐀¹_k`.  Then `f` is of finite type, and
an isomorphism over `U`.  A `U`-admissible blowup of `𝐀¹_k` is the blowup in a closed subscheme
`V(xⁿ)`, an effective Cartier divisor of a regular curve, hence an isomorphism; and since `X` is
integral, no nonzero local function on `X` is supported on the two origins, so the strict
transform of `X` is `X` itself.  But `X ⟶ 𝐀¹_k` is not an open immersion, not being injective.
The source's proof breaks where it applies Stacks 0879, which needs `f` separated.  Every use of
Stacks 087F in the source (Stacks 088Q, 0F47, 0F4A) applies it to a separated morphism.

## Main results

* `AlgebraicGeometry.Space.isFiniteType_strictTransformSpaceToBlowUp`: the strict transform of
  a morphism of finite type is of finite type.
* `AlgebraicGeometry.Space.exists_isBlowupAlong_isOpenImmersion_strictTransformSpaceToBlowUp`:
  the corrected statement of Stacks 087F, over the held inputs of Stacks 087E (Stacks 07VR and
  0873).

## Implementation notes

The proof is the source's, and runs parallel to the proof of Stacks 0GUW in
`AlgebraicGeometry.Space.exists_isBlowupAlong_isIso_strictTransformSpaceToBlowUp_of_isProper`:
blow up a finitely presented centre with complement `U`, which makes `U` scheme-theoretically
dense; flatten the strict transform by a second blowup (Stacks 087E); the second strict
transform is then an open immersion by Stacks 0879
(`AlgebraicGeometry.Space.isOpenImmersion_strictTransformSpaceToBlowUp`); the composite of the
two blowups is a blowup in a centre with complement `U` (Stacks 085Y, 086C), and its strict
transform is the iterated one (Stacks 0868, part (2)).

## References

* [Stacks Project, Tag 087F](https://stacks.math.columbia.edu/tag/087F)
* [Stacks Project, Tag 087E](https://stacks.math.columbia.edu/tag/087E)
* [Stacks Project, Tag 0868](https://stacks.math.columbia.edu/tag/0868)
* [Stacks Project, Tag 0879](https://stacks.math.columbia.edu/tag/0879)
* [Stacks Project, Tag 0GUW](https://stacks.math.columbia.edu/tag/0GUW)
-/

/- The main theorem carries no stacks attribute because it assumes `h07VR` and `h0873`, the two
inputs of Stacks 087E, in the shape they have in
`exists_isBlowupAlong_isFlat_isFinitePresentation_strictTransformSpaceToBlowUp`. The tag 087F,
with the correction described above, is attached to the form that assumes neither,
`exists_isBlowupAlong_isOpenImmersion_strictTransformSpaceToBlowUp_unconditional`. Part (2) of
Stacks 0868 is `exists_strictTransformSpace_comp_iso_unconditional`. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The strict transform of a morphism of finite type is of finite type**: it is a closed
immersion into a base change. -/
theorem isFiniteType_strictTransformSpaceToBlowUp {A X A' : AlgebraicSpaces B S hS}
    (f : X ⟶ A) (b : A' ⟶ A) (E : Subfunctor A'.1) (hf : IsFiniteType B S hS f.hom) :
    IsFiniteType B S hS (strictTransformSpaceToBlowUp B S hS f b E).hom := by
  have hsnd : IsFiniteType B S hS (strictTransformPullbackToBlowUp B S hS f b).hom :=
    (isFiniteType_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f b) hf
  exact isFiniteType_comp' B S hS _ _ (strictTransformPullback B S hS f b).2 A'.2
    (isFiniteType_of_isClosedImmersion B S hS _ (strictTransform B S hS f b E).2.2) hsnd

/-- **Stacks 087F, corrected, over Stacks 07VR and 0873 (`h07VR`, `h0873`).**  Let
`f : X ⟶ A` be a morphism of algebraic spaces over `S` and let `U ⊆ A` be an open subspace.
Assume that `A` is quasi-compact and quasi-separated, that `U` is quasi-compact, that `f` is of
finite type **and separated**, and that `f⁻¹(U) ⟶ U` is an isomorphism.  Then there is a
`U`-admissible blowup `b : A' ⟶ A`, with centre `Z`, such that `b⁻¹(U)` is
scheme-theoretically dense in `A'` and the strict transform of `X` is an open immersion into
`A'`.

Without separatedness the statement is false; see the module documentation.  The hypotheses
`h07VR` and `h0873` are the statements of Stacks 07VR and 0873, the held inputs of Stacks 087E
(`exists_isBlowupAlong_isFlat_isFinitePresentation_strictTransformSpaceToBlowUp`). -/
theorem exists_isBlowupAlong_isOpenImmersion_strictTransformSpaceToBlowUp
    (hZ : B.Contains (⊤_ Scheme.{u})) {A X : AlgebraicSpaces B S hS} (f : X ⟶ A)
    (U : OpenSubspaces B S hS A.1)
    (hAqc : IsQuasiCompactSpace B S hS A.1) (hAqs : IsAbsolutelyQuasiSeparated B S hS hZ A.1)
    (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor)
    (hft : IsFiniteType B S hS f.hom) (hsep : IsSeparated B S hS f.hom)
    (hiso : IsIso (pullback.snd f.hom U.1.ι))
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
            IsSchemeTheoreticallyDense B S hS (U.1.preimage b.hom) ∧
              IsOpenImmersion B S hS
                (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)).hom := by
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
  have hUZ₀ : Disjoint (subspacePointSet B S hS A.1 U.1) (subspacePointSet B S hS A.1 Z₀.1) :=
    hZ₀pts ▸ disjoint_compl_right
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
  -- The strict transform `X₁ ⟶ A₁`: of finite type, separated, an isomorphism over `U₁`.
  set f₁ := strictTransformSpaceToBlowUp B S hS f b₁ (Z₀.1.preimage b₁.hom) with hf₁def
  have hf₁ft : IsFiniteType B S hS f₁.hom := isFiniteType_strictTransformSpaceToBlowUp f b₁ _ hft
  have hf₁sep : IsSeparated B S hS f₁.hom := isSeparated_strictTransformSpaceToBlowUp f b₁ _ hsep
  have hf₁iso : IsIso (pullback.snd f₁.hom U₁.1.ι) :=
    isIso_pullbackSnd_strictTransformSpaceToBlowUp f b₁ Z₀ hb₁ U hUZ₀ hiso
  -- Flattening by blowing up.
  obtain ⟨A₂, b₂, Z₁, hZ₁fp, hU₁Z₁, hb₂, hflat₂, hfp₂⟩ :=
    exists_isBlowupAlong_isFlat_isFinitePresentation_strictTransformSpaceToBlowUp hZ h07VR
      h0873 f₁ U₁ hA₁qc hA₁qs hU₁qc hf₁ft (isQuasiSeparated_of_isSeparated B S hS hf₁sep)
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
  have hUY : Disjoint (subspacePointSet B S hS A.1 U.1) (subspacePointSet B S hS A.1 Y.1) :=
    hYpts ▸ disjoint_compl_right
  -- The second strict transform `X₂ ⟶ A₂` is an open immersion, and `U` is dense in `A₂`.
  set f₂ := strictTransformSpaceToBlowUp B S hS f₁ b₂ (Z₁.1.preimage b₂.hom) with hf₂def
  have hU₂dense : IsSchemeTheoreticallyDense B S hS (U₁.1.preimage b₂.hom) :=
    isSchemeTheoreticallyDense_preimage_of_isBlowupAlong_of_isSchemeTheoreticallyDense b₂ Z₁ hb₂
      U₁.1 hU₁dense
  have hf₂open : IsOpenImmersion B S hS f₂.hom :=
    isOpenImmersion_strictTransformSpaceToBlowUp f₁ b₂ Z₁ hb₂ U₁ hU₁Z₁ hU₁ι hU₁dense
      hf₁sep hf₁iso hflat₂ (isFiniteType_strictTransformSpaceToBlowUp f₁ b₂ _ hf₁ft).1
  -- The strict transform along the composite is the second strict transform.
  obtain ⟨k, j, -, hk, hj⟩ :=
    exists_strictTransformSpace_comp_iso_unconditional B S hS f b₁ b₂ Z₀ Z₁ Y hb₁ hb₂ hYcomp hYb
  refine ⟨A₂, b₂ ≫ b₁, Y, hYfp, hUY, hYb, ?_, ?_⟩
  · rw [show (b₂ ≫ b₁).hom = b₂.hom ≫ b₁.hom from rfl, Subfunctor.preimage_comp]
    exact hU₂dense
  have hcomp : j.hom ≫ strictTransformSpaceToBlowUp B S hS f (b₂ ≫ b₁)
      (Y.1.preimage (b₂ ≫ b₁).hom) = f₂ := by
    show j.hom ≫ strictTransformSpaceι B S hS f (b₂ ≫ b₁) (Y.1.preimage (b₂ ≫ b₁).hom) ≫
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
  show IsOpenImmersion B S hS (j.inv.hom ≫ f₂.hom)
  exact isOpenImmersion_comp B S hS _ _ (isOpenImmersion_of_isIso B S hS _) hf₂open

end AlgebraicGeometry.Space

end

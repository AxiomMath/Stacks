module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImmersionImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImmersionFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactSchemeTheoreticDensity
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactSchemeTheoreticImageDense
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableAtlasTest

/-!
# An immersion is a dense open subspace of its scheme-theoretic image

Let `S` be a scheme contained in a big fppf site `B` and let `h : Z ⟶ X` be an immersion of
algebraic spaces over `S` which is either quasi-compact or has reduced source. Write
`Z̄ ⊆ X` for the scheme-theoretic image of Stacks 082X. This file proves **Stacks 088G**: the
morphism `Z ⟶ Z̄` is an open immersion, its range is an open subspace of `Z̄`, that open
subspace is scheme-theoretically dense in `Z̄`, and the image of the points of `Z` is dense in
the points of `Z̄`.

## Main results

* `schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_qc_or_reduced`: the
  scheme-theoretic image of a morphism which is quasi-compact or has reduced source commutes
  with étale base change of the target.
* `isOpenImmersion_of_full_schemeTheoreticImage_of_qc_or_reduced`:
  an immersion which is quasi-compact or has reduced source and whose scheme-theoretic image is
  the whole target is an open immersion.
* `isOpenImmersion_toSchemeTheoreticImage_of_qc_or_reduced`:
  **Stacks 088G**, the morphism onto the scheme-theoretic image is an open immersion.
* `isOpenSubspace_range_toSchemeTheoreticImage_of_qc_or_reduced`:
  **Stacks 088G**, its range is an open subspace of the scheme-theoretic image.
* `isSchemeTheoreticallyDense_range_toSchemeTheoreticImage_of_qc_or_reduced`:
  **Stacks 088G**, that open subspace is scheme-theoretically dense.
* `denseRange_pointsMap_toSchemeTheoreticImage_of_qc_or_reduced`:
  **Stacks 088G**, the source is topologically dense in the scheme-theoretic image.

## References

* [Stacks Project, Tag 01RG](https://stacks.math.columbia.edu/tag/01RG)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 082X](https://stacks.math.columbia.edu/tag/082X)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
* [Stacks Project, Tag 0830](https://stacks.math.columbia.edu/tag/0830)
* [Stacks Project, Tag 0834](https://stacks.math.columbia.edu/tag/0834)
* [Stacks Project, Tag 088G](https://stacks.math.columbia.edu/tag/088G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_ImmersionSchemeTheoreticallyDenseOpen :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_ImmersionSchemeTheoreticallyDenseOpen
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_ImmersionSchemeTheoreticallyDenseOpen B S hS).has_limit _

/- Lean v4.35.0: instance search for these limits on presheaves of the big fppf site times out;
supply them directly. -/
local instance (J : Type) : HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

/-! ### Étale localization under either hypothesis -/

section EtaleLocal

variable {Z X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The scheme-theoretic image commutes with étale base change of the target** for a morphism
of algebraic spaces over `S` which is quasi-compact or whose source is reduced. -/
theorem schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_qc_or_reduced
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X) (f : Z ⟶ X)
    (hq_or_hr : IsQuasiCompact B S hS f ∨
      HasEtaleLocalProperty B S hS Z (fun W : Scheme.{u} => IsReduced W))
    (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (g : V ⟶ X) (hV : IsAlgebraicSpace B S hS V)
    (hg : IsEtale B S hS g) :
    schemeTheoreticImageSubfunctor B S hS (pullback.snd f g) =
      (schemeTheoreticImageSubfunctor B S hS f).preimage g :=
  hq_or_hr.elim
    (fun hq => schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_isQuasiCompact'
      B S hS f g hZ hX hV hq hg)
    (fun hr => schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale B S hS f g hZ hX hV hr hg)

end EtaleLocal

/-! ### Open immersions onto a full scheme-theoretic image -/

section Criterion

variable {Z X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The scheme-theoretic image of the second projection of a pullback square is the one of
the canonical `pullback.snd`. -/
private theorem schemeTheoreticImageSubfunctor_eq_of_isPullback
    {P Q R T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : P ⟶ R} {g : Q ⟶ R} {a : T ⟶ P} {b : T ⟶ Q}
    (hsq : IsPullback a b f g) :
    schemeTheoreticImageSubfunctor B S hS b =
      schemeTheoreticImageSubfunctor B S hS (pullback.snd f g) := by
  rw [← hsq.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback f g)]
  have : Epi (hsq.isoIsPullback _ _ (IsPullback.of_hasPullback f g)).hom :=
    @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom _)
  exact schemeTheoreticImageSubfunctor_comp_of_epi B S hS _ _

/-- The inverse of the isomorphism onto the range of a monomorphism `g` composes with `g` to the
inclusion of the range. -/
private theorem asIso_toRange_inv_comp {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : P ⟶ Q)
    [Mono g] : (asIso (Subfunctor.toRange g)).inv ≫ g = (Subfunctor.range g).ι :=
  (Iso.inv_comp_eq _).2 (Subfunctor.toRange_ι _).symm

/-- **A morphism of the big fppf category over `S` whose scheme-theoretic image subfunctor is
the whole target has vanishing kernel ideal sheaf.** -/
private theorem ker_eq_bot_of_schemeTheoreticImageSubfunctor_yoneda_eq_top
    {A U : BigFppfOver B S hS} (m : A ⟶ U)
    (hfull : schemeTheoreticImageSubfunctor B S hS (yoneda.map m) = ⊤) :
    ((BigFppfOver.toScheme B S hS).map m).ker = ⊥ := by
  have hmem : (𝟙 U) ∈ (schemeTheoreticImageSubfunctor B S hS (yoneda.map m)).obj (op U) := by
    rw [hfull]
    trivial
  have hle := ker_le_of_mem_schemeTheoreticImageSubfunctor B S hS m (𝟙 U) hmem
  have hid : ((BigFppfOver.toScheme B S hS).map (𝟙 U)).ker = ⊥ := by
    rw [CategoryTheory.Functor.map_id]
    exact Scheme.Hom.ker_eq_bot_of_isIso _
  rw [hid] at hle
  exact le_bot_iff.1 hle

/-- **An immersion of schemes with vanishing kernel ideal sheaf which is quasi-compact or has
reduced source is an open immersion.** -/
private theorem isOpenImmersion_of_ker_eq_bot {V W : Scheme.{u}} (m : V ⟶ W)
    [AlgebraicGeometry.IsImmersion m]
    (hq_or_hr : QuasiCompact m ∨ IsReduced V) (hker : m.ker = ⊥) :
    AlgebraicGeometry.IsOpenImmersion m := by
  have : IsIso m.imageι := by
    rwa [AlgebraicGeometry.IsClosedImmersion.isIso_iff_ker_eq_bot, Scheme.Hom.imageι,
      Scheme.IdealSheafData.ker_subschemeι]
  have : AlgebraicGeometry.IsOpenImmersion m.toImage := isOpenImmersion_toImage m hq_or_hr
  rw [← Scheme.Hom.toImage_imageι m]
  infer_instance

/-- **An immersion of algebraic spaces over `S` which is quasi-compact or has reduced source and
whose scheme-theoretic image is the whole target is an open immersion.** -/
theorem isOpenImmersion_of_full_schemeTheoreticImage_of_qc_or_reduced
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X) (f : Z ⟶ X)
    (hf : IsImmersion B S hS f)
    (hq_or_hr : IsQuasiCompact B S hS f ∨
      HasEtaleLocalProperty B S hS Z (fun W : Scheme.{u} => IsReduced W))
    (hfull : schemeTheoreticImageSubfunctor B S hS f = ⊤) :
    IsOpenImmersion B S hS f := by
  obtain ⟨U, φ, hs, he⟩ := hX.exists_atlas
  have hrep : yoneda.relativelyRepresentable f := hf.rep
  have him : AlgebraicGeometry.IsImmersion
    ((BigFppfOver.toScheme B S hS).map (hrep.snd φ)) := hf.property_snd φ
  have hφ : IsEtale B S hS φ := isEtale_of_presheafEtale B S hS φ he
  have hU : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hbc : schemeTheoreticImageSubfunctor B S hS (pullback.snd f φ) = ⊤ := by
    rw [schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_qc_or_reduced B S hS hZ hX f
      hq_or_hr _ φ hU hφ, hfull, Subfunctor.preimage_eq_top_iff]
    exact le_top
  have hsq : IsPullback (hrep.fst φ) (yoneda.map (hrep.snd φ)) f φ := hrep.isPullback φ
  have hfullm : schemeTheoreticImageSubfunctor B S hS (yoneda.map (hrep.snd φ)) = ⊤ := by
    rw [schemeTheoreticImageSubfunctor_eq_of_isPullback B S hS hsq, hbc]
  have hker := ker_eq_bot_of_schemeTheoreticImageSubfunctor_yoneda_eq_top B S hS (hrep.snd φ)
    hfullm
  have hcond : QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd φ)) ∨
      IsReduced ((BigFppfOver.toScheme B S hS).obj (hrep.pullback φ)) := by
    rcases hq_or_hr with hq | hr
    · exact Or.inl ((presheaf_quasiCompact_of_isQuasiCompact B S hS hrep hq).property_snd φ)
    · refine Or.inr ?_
      have _hsbc : MorphismProperty.IsStableUnderBaseChange
          (MorphismProperty.presheaf (MorphismProperty.inverseImage
            (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) :=
        MorphismProperty.relative_isStableUnderBaseChange _
      exact (exists_atlas_iff_forall_etale B S hS Z (fun W : Scheme.{u} => IsReduced W) hZ).1 hr
        (hrep.pullback φ) (hrep.fst φ)
        (MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip he)
  have hopen : AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (hrep.snd φ)) :=
    isOpenImmersion_of_ker_eq_bot _ hcond hker
  have _hsbc : MorphismProperty.IsStableUnderBaseChange
      (@AlgebraicGeometry.IsOpenImmersion.{u}) := inferInstance
  have _hlat : MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.IsOpenImmersion.{u}) Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  exact (presheaf_inverseImage_iff_atlas_snd B S hS
    (@AlgebraicGeometry.IsOpenImmersion.{u}) f hrep U φ hs he).2 hopen

end Criterion

/-! ### Scheme-theoretic density from étale localization -/

section Density

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A subspace whose scheme-theoretic closure is everything and whose scheme-theoretic image
commutes with étale base change of the ambient space is scheme-theoretically dense.** -/
theorem isSchemeTheoreticallyDense_of_schemeTheoreticClosure_eq_top
    (U : Subfunctor X)
    (h3 : ∀ (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (g : V ⟶ X),
      IsAlgebraicSpace B S hS V → IsEtale B S hS g →
        schemeTheoreticImageSubfunctor B S hS (pullback.snd U.ι g) =
          (schemeTheoreticImageSubfunctor B S hS U.ι).preimage g)
    (htop : schemeTheoreticClosure B S hS U = ⊤) :
    IsSchemeTheoreticallyDense B S hS U := by
  intro V hV φ hφ
  have htop' : schemeTheoreticImageSubfunctor B S hS U.ι = ⊤ := htop
  show schemeTheoreticImageSubfunctor B S hS (U.preimage φ).ι = ⊤
  rw [schemeTheoreticImageSubfunctor_eq_of_isPullback B S hS (Subfunctor.isPullback_preimage φ U),
    h3 V φ hV hφ, htop', Subfunctor.preimage_eq_top_iff]
  exact le_top

variable {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The range of a monomorphism of algebraic spaces over `S` whose scheme-theoretic image is
everything, and which is quasi-compact or has reduced source, is scheme-theoretically dense.** -/
theorem isSchemeTheoreticallyDense_range_of_qc_or_reduced
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X) (g : Z ⟶ X) [Mono g]
    (hq_or_hr : IsQuasiCompact B S hS g ∨
      HasEtaleLocalProperty B S hS Z (fun W : Scheme.{u} => IsReduced W))
    (hfull : schemeTheoreticImageSubfunctor B S hS g = ⊤) :
    IsSchemeTheoreticallyDense B S hS (Subfunctor.range g) := by
  have hrangeAlg : IsAlgebraicSpace B S hS (Subfunctor.range g).toFunctor :=
    isAlgebraicSpace_of_iso B S hS (asIso (Subfunctor.toRange g)) hZ
  have hsq : IsPullback (asIso (Subfunctor.toRange g)).inv (Subfunctor.range g).ι g (𝟙 X) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, asIso_toRange_inv_comp]⟩
  have hcond : IsQuasiCompact B S hS (Subfunctor.range g).ι ∨
      HasEtaleLocalProperty B S hS (Subfunctor.range g).toFunctor
        (fun W : Scheme.{u} => IsReduced W) :=
    hq_or_hr.imp (isQuasiCompact_of_isPullback B S hS hsq)
      (hasEtaleLocalProperty_of_isEtale B S hS hrangeAlg hZ
        (isEtale_of_isIso B S hS (asIso (Subfunctor.toRange g)).inv))
  have htop : schemeTheoreticClosure B S hS (Subfunctor.range g) = ⊤ := by
    show schemeTheoreticImageSubfunctor B S hS (Subfunctor.range g).ι = ⊤
    rwa [schemeTheoreticImageSubfunctor_congr_range B S hS (Subfunctor.range g).ι g hX
      (Subfunctor.range_ι _)]
  intro V hV k hk
  exact isSchemeTheoreticallyDense_of_schemeTheoreticClosure_eq_top B S hS _
    (schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_qc_or_reduced B S hS hrangeAlg
      hX (Subfunctor.range g).ι hcond) htop hV k hk

end Density

/-! ### Stacks 088G -/

section Main

variable {Z X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X) (h : Z ⟶ X)
    (hh : IsImmersion B S hS h)
    (hq_or_hr : IsQuasiCompact B S hS h ∨
      HasEtaleLocalProperty B S hS Z (fun W : Scheme.{u} => IsReduced W))

include hZ hX hh hq_or_hr

/-- **Stacks 088G, the first assertion.** The morphism from the source of an immersion of
algebraic spaces over `S` which is quasi-compact or has reduced source onto its scheme-theoretic
image is an open immersion. -/
theorem isOpenImmersion_toSchemeTheoreticImage_of_qc_or_reduced :
    IsOpenImmersion B S hS (toSchemeTheoreticImage B S hS h) := by
  have hC : IsClosedSubspace B S hS (schemeTheoreticImageSubfunctor B S hS h) :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS h hX
  have hsq : IsPullback (𝟙 Z) (toSchemeTheoreticImage B S hS h) h
      (schemeTheoreticImageSubfunctor B S hS h).ι :=
    isPullback_lift B S hS h (range_le_schemeTheoreticImageSubfunctor B S hS h)
  have _hsbc : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact isOpenImmersion_of_full_schemeTheoreticImage_of_qc_or_reduced B S hS hZ
    hC.1 (toSchemeTheoreticImage B S hS h) (MorphismProperty.of_isPullback hsq hh)
    (hq_or_hr.imp (isQuasiCompact_of_isPullback B S hS hsq) id)
    (schemeTheoreticImageSubfunctor_toSchemeTheoreticImage_eq_top B S hS h hX)

/-- **Stacks 088G, the second assertion.** The range of the morphism onto the scheme-theoretic
image is an open subspace of that image. -/
theorem isOpenSubspace_range_toSchemeTheoreticImage_of_qc_or_reduced :
    IsOpenSubspace B S hS (Subfunctor.range (toSchemeTheoreticImage B S hS h)) := by
  have hopen := isOpenImmersion_toSchemeTheoreticImage_of_qc_or_reduced B S hS hZ hX h hh hq_or_hr
  have : Mono (toSchemeTheoreticImage B S hS h) :=
    mono_of_isOpenImmersion B S hS _ hopen
  refine ⟨isAlgebraicSpace_of_iso B S hS
    (asIso (Subfunctor.toRange (toSchemeTheoreticImage B S hS h))) hZ, ?_⟩
  rw [← asIso_toRange_inv_comp B S hS (toSchemeTheoreticImage B S hS h)]
  exact MorphismProperty.RespectsIso.precomp _ _ _ hopen

/-- **Stacks 088G, the third assertion.** The open subspace of the scheme-theoretic image which
the source is identified with is scheme-theoretically dense in that image. -/
theorem isSchemeTheoreticallyDense_range_toSchemeTheoreticImage_of_qc_or_reduced :
    IsSchemeTheoreticallyDense B S hS
      (Subfunctor.range (toSchemeTheoreticImage B S hS h)) := by
  have hC : IsClosedSubspace B S hS (schemeTheoreticImageSubfunctor B S hS h) :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS h hX
  have hopen := isOpenImmersion_toSchemeTheoreticImage_of_qc_or_reduced B S hS hZ hX h hh hq_or_hr
  have : Mono (toSchemeTheoreticImage B S hS h) :=
    mono_of_isOpenImmersion B S hS _ hopen
  have hsqg : IsPullback (𝟙 Z) (toSchemeTheoreticImage B S hS h) h
      (schemeTheoreticImageSubfunctor B S hS h).ι :=
    isPullback_lift B S hS h (range_le_schemeTheoreticImageSubfunctor B S hS h)
  intro V hV k hk
  exact isSchemeTheoreticallyDense_range_of_qc_or_reduced B S hS hZ hC.1
    (toSchemeTheoreticImage B S hS h)
    (hq_or_hr.imp (isQuasiCompact_of_isPullback B S hS hsqg) id)
    (schemeTheoreticImageSubfunctor_toSchemeTheoreticImage_eq_top B S hS h hX) hV k hk

/-- **Stacks 088G, the fourth assertion.** The source of an immersion of algebraic spaces over
`S` which is quasi-compact or has reduced source is topologically dense in its scheme-theoretic
image. -/
theorem denseRange_pointsMap_toSchemeTheoreticImage_of_qc_or_reduced :
    DenseRange (pointsMap B S hS Z (toSchemeTheoreticImage B S hS h)) :=
  denseRange_pointsMap_toSchemeTheoreticImage B S hS h hZ hX
    (schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_qc_or_reduced B S hS hZ hX h
      hq_or_hr)

end Main

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.ProjectiveMorFunctorsBounded
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctorClosedImmersionLocus
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeMorphismAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasiAffineClosedInFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

/-!
# Relative morphism functors of H-projective schemes (towards Stacks 0D53)

Let `U` be an affine object of the big fppf site over `Spec ℤ` and let `q₁ : Z₁ ⟶ U`,
`q₂ : Z₂ ⟶ U` be H-projective, with `q₁` flat, proper and of finite presentation and `q₂` proper
and of finite presentation. Then `Mor_U(Z₁, Z₂)` is an algebraic space, with an étale atlas whose
size is bounded in terms of the size of `U` alone.

## The argument

* `Z₁ ×_U Z₂ ⟶ U` is H-projective (Stacks 01WF and 01WE), so there is a closed immersion
  `Z₁ ×_U Z₂ ⟶ ℙᴺ_U` over `U`.
* The Hilbert functor of `Z₁ ×_U Z₂ ⟶ U` maps to that of `ℙᴺ_U ⟶ U` by a closed immersion
  (Stacks 0DPF, `AlgebraicGeometry.Space.isClosedImmersion_hilbertModelMapOfClosed`), read in the
  canonical model of the first and in a model of the second which is an algebraic space with an
  atlas of bounded size (`AlgebraicGeometry.C1590Private.ProjectiveSpaceHilbertModelsBounded`).
* `Mor_U(Z₁, Z₂)` maps to the Hilbert functor of `Z₁ ×_U Z₂` by an open immersion, its graph
  (Stacks 0D1A and 0D1B, `AlgebraicGeometry.Space.morToHilbertModel_isOpenImmersion`).

The composite `Mor_U(Z₁, Z₂) ⟶ Hilb_{ℙᴺ_U/U}` is a representable immersion into an algebraic
space, so `Mor_U(Z₁, Z₂)` is an algebraic space, and the base change of the atlas of
`Hilb_{ℙᴺ_U/U}` along it is an atlas of `Mor_U(Z₁, Z₂)` whose source is a subscheme of the source
of that atlas, hence of bounded size (`AlgebraicGeometry.Scheme.size_le_of_mono`).

## Main results

* `AlgebraicGeometry.C1590Private.isProjectiveMorphism_toScheme_map_pullback_snd_comp`: the fibre
  product of two H-projective objects of the site over a third is H-projective over it.
* `projectiveMorFunctorsBounded_of_projectiveSpaceHilbertModelsBounded` (in the namespace
  `AlgebraicGeometry.C1590Private`): step E of the diagonal of `Curves`.

## References

* [Stacks Project, Tag 0D53](https://stacks.math.columbia.edu/tag/0D53)
* [Stacks Project, Tag 0DPF](https://stacks.math.columbia.edu/tag/0DPF)
* [Stacks Project, Tag 0D1B](https://stacks.math.columbia.edu/tag/0D1B)
* [Stacks Project, Tag 01WE](https://stacks.math.columbia.edu/tag/01WE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.C1590Private

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **The fibre product of two H-projective objects of the site is H-projective.** For
`q₁ : Z₁ ⟶ U` and `q₂ : Z₂ ⟶ U` in the big fppf site over `Spec ℤ` whose underlying morphisms of
schemes are H-projective, so is that of `Z₁ ×_U Z₂ ⟶ U`: it is the base change of `q₁` along `q₂`
(Stacks 01WF) followed by `q₂` (Stacks 01WE). -/
theorem isProjectiveMorphism_toScheme_map_pullback_snd_comp {U Z₁ Z₂ : BigFppfOver B integerBase hZ}
    (q₁ : Z₁ ⟶ U) (q₂ : Z₂ ⟶ U)
    (hq₁ : IsProjectiveMorphism ((BigFppfOver.toScheme B integerBase hZ).map q₁))
    (hq₂ : IsProjectiveMorphism ((BigFppfOver.toScheme B integerBase hZ).map q₂)) :
    IsProjectiveMorphism
      ((BigFppfOver.toScheme B integerBase hZ).map (pullback.snd q₁ q₂ ≫ q₂)) := by
  have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B integerBase hZ) := by
    dsimp only [BigFppfOver.toScheme]
    infer_instance
  have h₁ : IsProjectiveMorphism (pullback.snd ((BigFppfOver.toScheme B integerBase hZ).map q₁)
      ((BigFppfOver.toScheme B integerBase hZ).map q₂) ≫
        (BigFppfOver.toScheme B integerBase hZ).map q₂) :=
    (hq₁.baseChange _).comp hq₂
  refine IsProjectiveMorphism.of_iso
    (PreservesPullback.iso (BigFppfOver.toScheme B integerBase hZ) q₁ q₂).symm (Iso.refl _) ?_ h₁
  rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id, Functor.map_comp, ← Category.assoc,
    PreservesPullback.iso_inv_snd]

/-- The closed immersion `i : Z₁ ×_U Z₂ ⟶ P` over `s : P ⟶ U`, read as a closed immersion of
algebraic spaces from the ambient space of the graph construction to `P`, over `U`. -/
theorem exists_isClosedImmersion_graphAmbient_comp_eq
    {U Z₁ Z₂ P : BigFppfOver B integerBase hZ} (q₁ : Z₁ ⟶ U) (q₂ : Z₂ ⟶ U) (s : P ⟶ U)
    (hZ₁ : IsAlgebraicSpace B integerBase hZ (yoneda.obj Z₁))
    (hZ₂ : IsAlgebraicSpace B integerBase hZ (yoneda.obj Z₂))
    (hU : IsAlgebraicSpace B integerBase hZ (yoneda.obj U)) (i : pullback q₁ q₂ ⟶ P)
    (hi : IsClosedImmersion ((BigFppfOver.toScheme B integerBase hZ).map i))
    (his : i ≫ s = pullback.snd q₁ q₂ ≫ q₂) :
    ∃ π : Space.graphAmbient B integerBase hZ (yoneda.map q₁) (yoneda.map q₂) hZ₁ hZ₂ hU ⟶
        schemeSpace P,
      π ≫ schemeSpaceMap s =
        Space.graphAmbientMap B integerBase hZ (yoneda.map q₁) (yoneda.map q₂) hZ₁ hZ₂ hU ∧
      Space.IsClosedImmersion B integerBase hZ π.hom := by
  let eY := PreservesPullback.iso yoneda q₁ q₂
  refine ⟨ObjectProperty.homMk (eY.inv ≫ yoneda.map i), ?_, ?_⟩
  · apply ObjectProperty.hom_ext
    change eY.inv ≫ yoneda.map i ≫ yoneda.map s =
      pullback.fst (yoneda.map q₁) (yoneda.map q₂) ≫ yoneda.map q₁
    rw [← Functor.map_comp, his, Functor.map_comp, ← Category.assoc,
      PreservesPullback.iso_inv_snd]
    exact pullback.condition.symm
  · exact MorphismProperty.RespectsIso.precomp _ eY.inv _
      (Space.presheaf_yoneda_map_of_inverseImage B integerBase hZ inferInstance i hi)

variable (B hZ) in
/-- **Step E of the diagonal of `Curves`.** If the Hilbert functors of the projective spaces over
affine objects of the site have algebraic models with atlases of bounded size, then so do the
relative morphism functors of H-projective schemes over affine objects of the site. -/
theorem projectiveMorFunctorsBounded_of_projectiveSpaceHilbertModelsBounded
    (hD : ProjectiveSpaceHilbertModelsBounded B hZ) : ProjectiveMorFunctorsBounded B hZ := by
  intro μ hμ
  choose κ hκ hD' using fun n => hD n μ hμ
  refine ⟨⨆ n, (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ κ n,
    Cardinal.lift_iSup_lt_of_lt_cof_ord (by simpa using B.aleph0_lt_cutoff_cof)
    fun n => B.cutoff_isStrongPrelimit (B.cutoff_isStrongPrelimit (hκ n)), ?_⟩
  intro U Z₁ Z₂ q₁ q₂ hU hUμ hq₁ hq₂ hflat hprop hfp hprop₂ hfp₂
  -- the closed embedding of `Z₁ ×_U Z₂` into `ℙᴺ_U` over `U`
  obtain ⟨N, i, hi, hif⟩ := isProjectiveMorphism_toScheme_map_pullback_snd_comp q₁ q₂ hq₁ hq₂
  let i' : pullback q₁ q₂ ⟶ ProjectiveQuot.projectiveSite B N U := CurveFamily.homOfScheme i
  have hi' : i' ≫ ProjectiveQuot.projectiveSiteStructure B N U = pullback.snd q₁ q₂ ≫ q₂ :=
    (BigFppfOver.toScheme B integerBase hZ).map_injective (by rwa [Functor.map_comp])
  -- read on the algebraic spaces of the graph construction
  have hZ₁ := isAlgebraicSpace_yoneda B integerBase hZ Z₁
  have hZ₂ := isAlgebraicSpace_yoneda B integerBase hZ Z₂
  have hU' := isAlgebraicSpace_yoneda B integerBase hZ U
  obtain ⟨π, hπ, hclosed⟩ :=
    exists_isClosedImmersion_graphAmbient_comp_eq q₁ q₂ _ hZ₁ hZ₂ hU' i' hi hi'
  -- the model of `Hilb_{ℙᴺ_U/U}` and the two immersions
  obtain ⟨MY, A, a, hMY, ha₁, ha₂, ha₃⟩ := hD' N U hU hUμ
  have hfpY : Space.IsFinitePresentation B integerBase hZ
      (schemeSpaceMap (ProjectiveQuot.projectiveSiteStructure B N U)).hom :=
    Space.isFinitePresentation_yoneda_map B integerBase hZ _
      (ProjectiveQuot.finitePresentation_projectiveSpaceOver N _)
  let MX := Space.HilbertPresheafModel.canonical
    (Space.graphAmbientMap B integerBase hZ (yoneda.map q₁) (yoneda.map q₂) hZ₁ hZ₂ hU')
  let r := Space.morToHilbertModel (yoneda.map q₁) (yoneda.map q₂) hZ₁ hZ₂ hU' MX hprop₂.1 hfp
    hflat hprop ≫ Space.hilbertModelMapOfClosed hπ hclosed MX MY
  have hr : Space.IsImmersion B integerBase hZ r :=
    Space.isImmersion_comp B integerBase hZ _ _
      (Space.isImmersion_of_isOpenImmersion B integerBase hZ
        (Space.morToHilbertModel_isOpenImmersion (yoneda.map q₁) (yoneda.map q₂) hZ₁ hZ₂ hU' MX
          hprop₂.1 hfp hflat hprop))
      (Space.isImmersion_of_isClosedImmersion B integerBase hZ
        (Space.isClosedImmersion_hilbertModelMapOfClosed hπ hclosed hfpY MX MY))
  refine ⟨isAlgebraicSpace_of_relativelyRepresentable B integerBase hZ r hr.1 hMY, ?_⟩
  -- the atlas: the base change of the atlas of the model along `r`
  have hpb := (hr.1.isPullback a).flip
  refine ⟨hr.1.pullback a, hr.1.fst a,
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hpb ha₁,
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hpb ha₂, ?_⟩
  have himm : IsImmersion ((BigFppfOver.toScheme B integerBase hZ).map (hr.1.snd a)) :=
    hr.2 a _ _ hpb.flip
  refine (Scheme.size_le_of_mono ((BigFppfOver.toScheme B integerBase hZ).map (hr.1.snd a))).trans
    ((max_le ?_ ?_).trans (le_ciSup Cardinal.bddAbove_of_small N))
  · exact power_le_power_left two_ne_zero ((Scheme.mk_le_two_pow_size _).trans
      (power_le_power_left two_ne_zero ha₃))
  · exact ha₃.trans ((cantor _).le.trans (cantor _).le)

end AlgebraicGeometry.C1590Private

end

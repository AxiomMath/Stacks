module

public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryProjectiveSectionsAlongFibreSite
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsFibreProductResidueIso

/-!
# An elementary étale chart of the base whose base change has its fibre covered

Let `f : X ⟶ Y` be a morphism of finite presentation of algebraic spaces over `S`, let `𝓕` be a
quasi-coherent `𝒪_X`-module of finite presentation, flat over `Y`, and let `y ∈ |Y|`.  This file
produces, from Stacks 0CVZ in its pointed elementary form, an étale morphism `q ≫ b₀ : A ⟶ Y`
from an affine scheme with a point `a₀` over `y`, an étale chart `Y' ⟶ X` from an affine scheme
with a morphism `h : Y' ⟶ A` over `f`, such that

* the sections of the pullback of `𝓕` to `Y'` are projective over `Γ(A, 𝒪_A)`, and
* in *every* fibre product `P = X ×_Y A`, every point lying over `a₀` is the image of a point of
  `Y'` under the induced morphism `Y' ⟶ P`.

The second clause is what Stacks 0CVZ does not give: it covers the fibre of the base change over
`a₀`, not merely the fibre of `f` over `y`.  It holds because `A ⟶ V₀` is an elementary étale
neighbourhood of the base point of an affine étale chart `V₀` of `Y`, so that points of
`X ×_Y A = (X ×_Y V₀) ×_{V₀} A` over `a₀` are determined by their image in `X ×_Y V₀`
(`AlgebraicGeometry.Space.eq_of_pointsMap_eq_of_isPullback_of_isIso_residueFieldMap`), and the
chart `Z` of `X ×_Y V₀` the construction starts from covers the fibre of `X ×_Y V₀` over the base
point.

This is the first half of the proof of Stacks 0CWC: the chart over which purity is spent.

## Main results

* `AlgebraicGeometry.Space.exists_elementary_chart_projective_sections_covering_baseChange_fibre`.

## References

* [Stacks Project, Tag 0CVZ](https://stacks.math.columbia.edu/tag/0CVZ)
* [Stacks Project, Tag 0CWC](https://stacks.math.columbia.edu/tag/0CWC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- **An elementary étale chart of the base whose base change has its fibre covered.**  See the
module docstring.  The output consists of an étale morphism `b₀ : h_{V₀} ⟶ Y`, an étale chart
`U` of `X`, affine objects `A` and `Y'` of the site, an étale morphism `q : A ⟶ V₀` inducing an
isomorphism of residue fields at the point `a₀` of `A`, which lies over `y`, an étale morphism
`r : Y' ⟶ U` and a morphism `h : Y' ⟶ A` over `f`, such that the sections of the pullback of
`𝓕|_U` along `r` are projective over `Γ(A, 𝒪_A)` (acting through `h`), and such that for every
fibre product `P` of `f` and `q ≫ b₀` and every morphism `s : h_{Y'} ⟶ P` over `r` and `h`,
every point of `|P|` over `a₀` lies in the image of `s`. -/
theorem exists_elementary_chart_projective_sections_covering_baseChange_fibre
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (𝓕 : Modules.{u, u} B S hS X hX) (y : points B S hS Y)
    (hfp : IsFinitePresentation B S hS f)
    (hqc : 𝓕.IsQuasicoherentOnSite)
    (h𝓕fp : SheafOfModules.IsFinitePresentationOnSite 𝓕)
    (hflat : IsFlatOver B S hS hX f 𝓕) :
    ∃ (V₀ : BigFppfOver B S hS) (b₀ : yoneda.obj V₀ ⟶ Y) (U : SmallEtale B S hS X)
      (A Y' : BigFppfOver B S hS) (q : A ⟶ V₀) (r : Y' ⟶ (SmallEtale.toOver B S hS X).obj U)
      (h : Y' ⟶ A) (a₀ : (BigFppfOver.toScheme B S hS).obj A),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b₀ ∧
      Etale ((BigFppfOver.toScheme B S hS).map q) ∧
      IsIso (((BigFppfOver.toScheme B S hS).map q).residueFieldMap a₀) ∧
      pointsMap B S hS _ (yoneda.map q ≫ b₀)
        ((pointsEquivScheme B S hS A).symm a₀) = y ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj A) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj Y') ∧
      Etale ((BigFppfOver.toScheme B S hS).map r) ∧
      (yoneda.map r ≫ U.obj.hom) ≫ f = yoneda.map h ≫ yoneda.map q ≫ b₀ ∧
      (∀ {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {pX : P ⟶ X} {pA : P ⟶ yoneda.obj A}
        (_ : IsPullback pX pA f (yoneda.map q ≫ b₀)) (s : yoneda.obj Y' ⟶ P)
        (_ : s ≫ pX = yoneda.map r ≫ U.obj.hom) (_ : s ≫ pA = yoneda.map h)
        (ξ : points B S hS P),
        pointsToScheme B S hS A (pointsMap B S hS P pA ξ) = a₀ →
        ξ ∈ Set.range (pointsMap B S hS _ s)) ∧
      (let M := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).obj
           (restrictToChart B S hS hX 𝓕 U)
       letI : Module Γ((BigFppfOver.toScheme B S hS).obj A, ⊤) Γ(M, ⊤) :=
         Module.compHom Γ(M, ⊤) ((BigFppfOver.toScheme B S hS).map h).appTop.hom
       Module.Projective Γ((BigFppfOver.toScheme B S hS).obj A, ⊤) Γ(M, ⊤)) := by
  classical
  -- An affine étale chart of the target through `y`.
  obtain ⟨V₀, b₀, hV₀aff, hbE, v, hv⟩ := exists_affine_etale_chart_at_point B S hS Y hY y
  obtain ⟨pv, hpv⟩ := Quot.exists_rep v
  have hpvc : pv.class B S hS (yoneda.obj V₀) = v := hpv
  -- The base change `W₀ = X ×_Y V₀` and an affine étale chart of it covering the fibre.
  have sq : IsPullback (pullback.fst f b₀) (pullback.snd f b₀) f b₀ :=
    IsPullback.of_hasPullback f b₀
  have hW : IsAlgebraicSpace B S hS (pullback f b₀) :=
    isAlgebraicSpace_pullback B S hS f b₀ hX (isAlgebraicSpace_yoneda B S hS V₀) hY
  have hpr₁E : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.fst f b₀) :=
    presheaf_of_isPullback B S hS sq.flip hbE
  have hpr₂qc : IsQuasiCompact B S hS (pullback.snd f b₀) :=
    isQuasiCompact_of_isPullback B S hS sq hfp.2.1
  have hTcompact : IsCompact (setFibre B S hS (pullback.snd f b₀) pv) :=
    isCompact_setFibre_of_isQuasiCompact B S hS hW (isAlgebraicSpace_yoneda B S hS V₀)
      (pullback.snd f b₀) hpr₂qc pv
  obtain ⟨Z, c, hZaff, hcE, hcover⟩ :=
    exists_affine_etale_chart_of_isCompact B S hS (pullback f b₀) hW hTcompact
  have hmul := isMultiplicative_presheaf_etale B S hS
  have hgE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (c ≫ pullback.fst f b₀) :=
    MorphismProperty.comp_mem _ _ _ hcE hpr₁E
  let U : SmallEtale B S hS X := ⟨CostructuredArrow.mk (c ≫ pullback.fst f b₀), hgE⟩
  let V : SmallEtale B S hS Y := ⟨CostructuredArrow.mk b₀, hbE⟩
  let k₀ : Z ⟶ V₀ := yoneda.preimage (c ≫ pullback.snd f b₀)
  have hk₀ : yoneda.map k₀ = c ≫ pullback.snd f b₀ := yoneda.map_preimage _
  have hsq : U.obj.hom ≫ f = yoneda.map k₀ ≫ V.obj.hom := by
    show (c ≫ pullback.fst f b₀) ≫ f = yoneda.map k₀ ≫ b₀
    rw [hk₀, Category.assoc, Category.assoc, sq.w]
  have hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X).obj U)) := hZaff
  have hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS Y).obj V)) := hV₀aff
  -- The morphism of charts is of finite presentation.
  have hk₀fp : FinitePresentation ((BigFppfOver.toScheme B S hS).map k₀) :=
    ⟨hfp.1 _ _ U.obj.hom V.obj.hom k₀ U.property V.property hsq.symm,
      (quasiCompact_iff_compactSpace _).mpr inferInstance, inferInstance⟩
  set vs := pointsToScheme B S hS V₀ v with hvs
  -- The pointed elementary form of Stacks 05KW on the chart morphism.
  obtain ⟨Y', A, r, q, h, a₀, hrE, hqE, hcomm, hqa, hres, hY'aff, hAaff, hcov, hproj⟩ :=
    exists_isAffine_elementary_etale_hom_projective_sections_along_fibre B S hS _ _ k₀
      (restrictToChart B S hS hX 𝓕 U) vs hk₀fp
      (isQuasicoherentOnCharts_of_isQuasicoherentOnSite B S hS ⟨X, hX⟩ 𝓕 hqc U)
      (isFinitePresentationOnCharts_of_isFinitePresentationOnSite B S hS ⟨X, hX⟩ 𝓕 hqc h𝓕fp U)
      (fun δ _ => hflat ⟨U, V, k₀, hsq⟩ δ)
  -- The base point.
  have hqv : pointsMap B S hS (yoneda.obj A) (yoneda.map q)
      ((pointsEquivScheme B S hS A).symm a₀) = v := by
    refine injective_pointsToScheme B S hS V₀ ?_
    rw [pointsToScheme_pointsMap_yoneda]
    show (BigFppfOver.toScheme B S hS).map q
      ((pointsEquivScheme B S hS A) ((pointsEquivScheme B S hS A).symm a₀)) = vs
    rw [Equiv.apply_symm_apply, hqa]
  have hyoneda : yoneda.map r ≫ yoneda.map k₀ = yoneda.map h ≫ yoneda.map q := by
    rw [← Functor.map_comp, ← Functor.map_comp, hcomm]
  have hsqfin : (yoneda.map r ≫ U.obj.hom) ≫ f = yoneda.map h ≫ yoneda.map q ≫ b₀ := by
    rw [Category.assoc, hsq, ← Category.assoc, hyoneda, Category.assoc]
    rfl
  refine ⟨V₀, b₀, U, A, Y', q, r, h, a₀, hbE, hqE, hres, ?_, hAaff, hY'aff, hrE, hsqfin,
    ?_, hproj⟩
  · rw [pointsMap_comp_apply, hqv, hv]
  -- The fibre of an arbitrary base change over `a₀` is covered.
  intro P pX pA sqP s hsX hsA ξ hξ
  let φ : P ⟶ pullback f b₀ := pullback.lift pX (pA ≫ yoneda.map q) (by
    rw [sqP.w, Category.assoc])
  have hφ₁ : φ ≫ pullback.fst f b₀ = pX := pullback.lift_fst _ _ _
  have hφ₂ : φ ≫ pullback.snd f b₀ = pA ≫ yoneda.map q := pullback.lift_snd _ _ _
  have sqφ : IsPullback φ pA (pullback.snd f b₀) (yoneda.map q) :=
    IsPullback.of_right (by rwa [hφ₁]) hφ₂ sq
  -- The image `w` of `ξ` in `W₀` lies over the base point, hence comes from the chart `Z`.
  set w := pointsMap B S hS P φ ξ with hw
  have hpAξ : pointsMap B S hS P pA ξ = (pointsEquivScheme B S hS A).symm a₀ :=
    injective_pointsToScheme B S hS A
      (hξ.trans ((pointsEquivScheme B S hS A).apply_symm_apply a₀).symm)
  have hw₂ : pointsMap B S hS _ (pullback.snd f b₀) w = v := by
    rw [hw, ← pointsMap_comp_apply, hφ₂, pointsMap_comp_apply, hpAξ, hqv]
  obtain ⟨z, hz⟩ := hcover (show w ∈ setFibre B S hS (pullback.snd f b₀) pv from
    hw₂.trans hpvc.symm)
  have hzk : (BigFppfOver.toScheme B S hS).map k₀ (pointsToScheme B S hS Z z) = vs := by
    rw [← pointsToScheme_pointsMap_yoneda, hk₀, pointsMap_comp_apply, hz, hw₂, hvs]
  obtain ⟨d, hd, hdk⟩ := hcov _ hzk
  set d' := (pointsEquivScheme B S hS Y').symm d
  have hbackD : pointsToScheme B S hS Y' d' = d :=
    (pointsEquivScheme B S hS Y').apply_symm_apply d
  have hrd : pointsMap B S hS _ (yoneda.map r) d' = z := by
    refine injective_pointsToScheme B S hS Z ?_
    rwa [pointsToScheme_pointsMap_yoneda, hbackD]
  have hsφ : s ≫ φ = yoneda.map r ≫ c := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hφ₁, hsX, Category.assoc]
      rfl
    · rw [Category.assoc, hφ₂, ← Category.assoc, hsA, Category.assoc, ← hk₀, hyoneda]
  refine ⟨d', eq_of_pointsMap_eq_of_isPullback_of_isIso_residueFieldMap B S hS sqφ a₀ ?_ ?_ hξ⟩
  · rw [← pointsMap_comp_apply, hsφ, pointsMap_comp_apply, hrd, hz]
  · rwa [← pointsMap_comp_apply, hsA, pointsToScheme_pointsMap_yoneda, hbackD]

end AlgebraicGeometry.Space

end

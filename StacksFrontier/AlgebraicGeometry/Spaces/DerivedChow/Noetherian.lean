module

public import StacksFrontier.AlgebraicGeometry.Morphisms.PseudoCoherentFrom
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.StandardAffineChart
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceProper
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtFinitePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowTwistWitness
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceFinitePresentationOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedChow.Datum
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedChow.Restriction
public import StacksFrontier.AlgebraicGeometry.Spaces.GraphTorIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedChow.StructureSheafPushforwardSingle
public import StacksFrontier.AlgebraicGeometry.Spaces.DualizingComplexEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealInjectionDevissageStep
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasiAffineClosedInFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsHenselianLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# The derived Chow lemma over a Noetherian ring

This file proves Stacks 0CTR for an algebraic space `X` separated and of finite presentation
over a Noetherian ring `A`: around every point `x ∈ |X|` there is a datum
`AlgebraicGeometry.Space.DerivedChowDatum`. This is the second paragraph of the source's proof;
the reduction of a general ring to this case is the first.

The construction is the source's. Choose an affine étale chart `u : U ⟶ X` through `x`, a closed
immersion of `U` into `𝔸ᵐ_A`, and let `j : U ⟶ ℙᵐ_A` be its composite with the standard affine
chart `𝔸ᵐ_A ⟶ ℙᵐ_A`. The graph `(u, j) : U ⟶ X ×_A ℙᵐ_A` lands in the open `X ×_A 𝔸ᵐ_A`, where it
is a closed immersion because `X` is separated; let `Z` be its scheme-theoretic image. The
scheme-theoretic image commutes with the étale base change to `X ×_A 𝔸ᵐ_A` (Stacks 082Z), so the
part `W` of `Z` over `V = 𝔸ᵐ_A` is the graph itself, isomorphic to `U`: over `V` the projection
`c : Z ⟶ ℙᵐ_A` is the closed immersion `U ⟶ 𝔸ᵐ_A`, and `b : W ⟶ X` is the étale chart `u`. The
open `V` here is the standard chart; this replaces the source's choice of an open meeting the
closure of `j(U)` in `j(U)` (the source's use of Stacks 0CP3). Since `A` is Noetherian, so is
`X ×_A ℙᵐ_A`, and `E = (b, c)_*𝒪_Z` is pseudo-coherent by Stacks 08IK.

## Main results

* `AlgebraicGeometry.Space.preimage_schemeTheoreticImageSubfunctor_comp_eq_range`: the part
  over an étale monomorphism of the scheme-theoretic image of a closed immersion into it.
* `AlgebraicGeometry.Space.exists_derivedChowDatum_torIndependentOverBase_of_isNoetherianRing`:
  Stacks 0CTR over a Noetherian ring, with the datum's closed immersion moreover Tor independent
  of every base change of `X ×_A V` along a morphism of schemes to `Spec A`.

## References

* [Stacks Project, Tag 0CTR](https://stacks.math.columbia.edu/tag/0CTR)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
* [Stacks Project, Tag 08IK](https://stacks.math.columbia.edu/tag/08IK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] HasDerivedCategory.standard

open DerivedChow

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on a big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_DerivedChowNoetherian (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_DerivedChowNoetherian
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

section GraphClosure

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The scheme-theoretic image of `Γ' ≫ g`, for a closed immersion `Γ'` and an étale
monomorphism `g` with `Γ' ≫ g` quasi-compact, has inverse image along `g` the range of `Γ'`:
its part over `g` is the closed subspace `Γ'` itself. -/
theorem preimage_schemeTheoreticImageSubfunctor_comp_eq_range
    (hU : IsAlgebraicSpace B S hS U) (hT : IsAlgebraicSpace B S hS T)
    (hT' : IsAlgebraicSpace B S hS T') (Γ' : U ⟶ T') (g : T' ⟶ T) [Mono g]
    (hΓ' : IsClosedImmersion B S hS Γ') (hg : IsEtale B S hS g)
    (hqc : IsQuasiCompact B S hS (Γ' ≫ g)) :
    (schemeTheoreticImageSubfunctor B S hS (Γ' ≫ g)).preimage g = Subfunctor.range Γ' := by
  rw [← schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_isQuasiCompact' B S hS
    (Γ' ≫ g) g hU hT hT' hqc hg]
  have hrange : Subfunctor.range (pullback.snd (Γ' ≫ g) g) = Subfunctor.range Γ' := by
    rw [Subfunctor.range_eq_preimage_of_isPullback (IsPullback.of_hasPullback (Γ' ≫ g) g).flip]
    ext c t
    have hinj : Function.Injective (g.app c) :=
      (mono_iff_injective (g.app c)).1 inferInstance
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, hinj (by simpa using hy)⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, by simp⟩
  have hsti : schemeTheoreticImageSubfunctor B S hS (pullback.snd (Γ' ≫ g) g) =
      schemeTheoreticImageSubfunctor B S hS Γ' := by
    simp only [schemeTheoreticImageSubfunctor, hrange]
  rw [hsti]
  exact le_antisymm
    (schemeTheoreticImageSubfunctor_le B S hS Γ'
      (isClosedSubspace_range_of_isClosedImmersion B S hS Γ' hU hΓ') le_rfl)
    (range_le_schemeTheoreticImageSubfunctor B S hS Γ')

end GraphClosure

/-- The closed immersion `W ⟶ X ×_S V` of a datum of the derived Chow lemma is Tor independent
(Stacks 08IP) of the base change of `X ×_S V` along every morphism of schemes `S' ⟶ S`. This is
the property of the datum over a Noetherian ring that survives a change of base ring
(Stacks 0CTQ); the derived Chow lemma over a general ring uses it. -/
def DerivedChowDatum.TorIndependentOverBase {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {X : AlgebraicSpaces B S hS} {x : points B S hS X.1}
    (D : DerivedChowDatum X x) : Prop :=
  ∀ (Ys : BigFppfOver B S hS) (Y' : AlgebraicSpaces B S hS)
    (κ : Y' ⟶ productOver X D.n D.contains D.v) (πY : Y'.1 ⟶ yoneda.obj Ys),
    IsPullback κ.hom πY ((isTerminal_yoneda_obj_base B S hS).from _)
      (yoneda.map (Over.homMk Ys.hom : Ys ⟶ Over.mk (𝟙 (B.obj hS)))) →
    TorIndependent (overOpen D.i D.v).2 Y'.2 (productOver X D.n D.contains D.v).2
      (overOpenToProductOver D.i D.v).hom κ.hom

section Noetherian

variable (B : BigFppfSite.{u}) {A : Type u} [CommRing A] (hA : B.Contains (Spec (.of A)))

/-- **The derived Chow datum over a Noetherian ring at a given affine étale chart.** Let `A` be
a Noetherian ring, `X` an algebraic space separated and of finite presentation over `A`, and
`b : U₀ ⟶ X` an étale morphism from an affine scheme. At the image of every point of `U₀` there
is a datum of the derived Chow lemma whose `W` is `U₀` over `X`, whose open `V` is an affine
space `𝔸ᵐ_A` and whose `W ⟶ V` is a closed immersion `U₀ ⟶ 𝔸ᵐ_A`; its closed immersion
`W ⟶ X ×_A V` is Tor independent of every base change along a morphism of schemes to
`Spec A`. -/
theorem exists_derivedChowDatum_of_chart [IsNoetherianRing A]
    (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (hsep : IsSeparated B (Spec (.of A)) hA (toBase B (Spec (.of A)) hA X).hom)
    (hfp : IsFinitePresentation B (Spec (.of A)) hA (toBase B (Spec (.of A)) hA X).hom)
    {Z₀ : BigFppfOver B (Spec (.of A)) hA} (b : yoneda.obj Z₀ ⟶ X.1)
    (hZ₀ : IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj Z₀))
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of A)) hA)).presheaf b)
    (a : points B (Spec (.of A)) hA (yoneda.obj Z₀)) :
    ∃ D : DerivedChowDatum X (pointsMap B (Spec (.of A)) hA _ b a), D.TorIndependentOverBase ∧
      ∃ eW : yoneda.obj Z₀ ≅ (overOpen D.i D.v).1,
        eW.inv ≫ b = (overOpenι D.i D.v ≫ D.i ≫ productFst X D.n D.contains).hom ∧
        ∃ (AS : BigFppfOver B (Spec (.of A)) hA) (eV : D.V ≅ schemeSpace AS) (jA : Z₀ ⟶ AS),
          IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj AS) ∧
          Flat (B.inclusion.map AS.hom) ∧ LocallyOfFinitePresentation (B.inclusion.map AS.hom) ∧
          _root_.AlgebraicGeometry.IsClosedImmersion
            ((BigFppfOver.toScheme B (Spec (.of A)) hA).map jA) ∧
          (overOpenToOpen D.i D.v).hom ≫ eV.hom.hom = eW.inv ≫ yoneda.map jA := by
  let Q := BigFppfOver.toScheme B (Spec (.of A)) hA
  let base : BigFppfOver B (Spec (.of A)) hA := baseSiteObj B (Spec (.of A)) hA
  have : IsAffine (Q.obj Z₀) := hZ₀
  let t₀ : Z₀ ⟶ base := Over.mkIdTerminal.from Z₀
  have hb' : (toBase B (Spec (.of A)) hA X).hom =
      (isTerminal_yoneda_obj_base B (Spec (.of A)) hA).from X.1 := rfl
  have hlfp : LocallyOfFinitePresentation (Q.map t₀) := by
    refine hfp.1 Z₀ base b (𝟙 _) t₀ hb
      (by
        have := isMultiplicative_presheaf_etale B (Spec (.of A)) hA
        exact MorphismProperty.id_mem _ _) ?_
    exact (isTerminal_yoneda_obj_base B (Spec (.of A)) hA).hom_ext _ _
  have : IsAffine (Q.obj base) := inferInstanceAs (IsAffine (Spec (.of A)))
  -- A closed immersion `c₀ : U₀ ⟶ 𝔸ᵐ_A` over `A`.
  obtain ⟨m, c₀, hc₀, hc₀S⟩ := exists_isClosedImmersion_affineSpace (Q.map t₀)
  -- Projective space `ℙᵐ_A` and its standard chart `𝔸ᵐ_A`, as objects of the site.
  let σ := ULift.{u} (Fin m)
  let e : σ ≃ {j : Fin (m + 1) // j ≠ 0} := Equiv.ulift.trans (finSuccAboveEquiv (0 : Fin (m + 1)))
  have hP : B.Contains (projectiveSpaceOver m (Spec (.of A))) :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
      (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A)) hA
  let aS := projectiveSpaceOver.affineChart m 0 e (Spec (.of A))
  have hAS : B.Contains 𝔸(σ; Spec (.of A)) := Scheme.size_lt_of_isOpenImmersion aS hP
  let P := projectiveSpaceSiteObj B (Spec (.of A)) hA m hP
  let AS : BigFppfOver B (Spec (.of A)) hA :=
    Over.mk (⟨𝔸(σ; Spec (.of A)) ↘ Spec (.of A)⟩ : B.obj hAS ⟶ B.obj hA)
  let aP : AS ⟶ P := Over.homMk ⟨aS⟩ (by
    ext1
    exact projectiveSpaceOver.affineChart_over m 0 e (Spec (.of A)))
  let jA : Z₀ ⟶ AS := Over.homMk ⟨c₀⟩ (by
    ext1
    refine hc₀S.trans ?_
    have h := Over.w t₀
    simp only [base, baseSiteObj, Over.mk_hom] at h
    exact congrArg (fun k => k.hom) h)
  -- The graph `Γ = (u, j) : h_{U₀} ⟶ X ×_A ℙᵐ_A` and its factorization `Γ'` through `X ×_A 𝔸ᵐ_A`.
  let T := product B (Spec (.of A)) hA X m hP
  let q := productSnd X m hP
  let V : AlgebraicSpaces B (Spec (.of A)) hA := schemeSpace AS
  let v : V ⟶ schemeSpace P := schemeSpaceMap aP
  let TV := productOver X m hP v
  let g := (productOverι X m hP v).hom
  let Γ : yoneda.obj Z₀ ⟶ pullback (toBase B (Spec (.of A)) hA X).hom
      (yoneda.map (projectiveSpaceSiteObjToBase B (Spec (.of A)) hA m hP)) :=
    pullback.lift b (yoneda.map (jA ≫ aP))
      ((isTerminal_yoneda_obj_base B (Spec (.of A)) hA).hom_ext _ _)
  have hΓq : Γ ≫ pullback.snd _ _ = yoneda.map jA ≫ yoneda.map aP :=
    (pullback.lift_snd _ _ _).trans (Functor.map_comp _ _ _)
  let Γ' : yoneda.obj Z₀ ⟶ pullback (pullback.snd (toBase B (Spec (.of A)) hA X).hom
      (yoneda.map (projectiveSpaceSiteObjToBase B (Spec (.of A)) hA m hP))) (yoneda.map aP) :=
    pullback.lift Γ (yoneda.map jA) hΓq
  have hΓ'g : Γ' ≫ pullback.fst _ _ = Γ := pullback.lift_fst _ _ _
  have hΓ'snd : Γ' ≫ pullback.snd _ _ = yoneda.map jA := pullback.lift_snd _ _ _
  have hTalg : IsAlgebraicSpace B (Spec (.of A)) hA (pullback (toBase B (Spec (.of A)) hA X).hom
      (yoneda.map (projectiveSpaceSiteObjToBase B (Spec (.of A)) hA m hP))) := T.2
  have hTValg : IsAlgebraicSpace B (Spec (.of A)) hA
      (pullback (pullback.snd (toBase B (Spec (.of A)) hA X).hom
        (yoneda.map (projectiveSpaceSiteObjToBase B (Spec (.of A)) hA m hP))) (yoneda.map aP)) :=
    TV.2
  have hUalg := isAlgebraicSpace_yoneda B (Spec (.of A)) hA Z₀
  -- `Γ'` is a closed immersion: its composite with the separated projection to `𝔸ᵐ_A` is `c₀`.
  have hjA : IsClosedImmersion B (Spec (.of A)) hA (yoneda.map jA) :=
    have := inverseImage_isStableUnderBaseChange B (Spec (.of A)) hA
      (P := @AlgebraicGeometry.IsClosedImmersion.{u}) inferInstance
    MorphismProperty.relative_map (F := yoneda)
      (show AlgebraicGeometry.IsClosedImmersion c₀ from hc₀)
  have hΓ' : IsClosedImmersion B (Spec (.of A)) hA Γ' :=
    isClosedImmersion_of_comp_of_isSeparated B (Spec (.of A)) hA Γ' (pullback.snd _ _)
      (by rw [hΓ'snd]; exact hjA)
      (isSeparated_pullback B (Spec (.of A)) hA _ _ (isSeparated_pullback B (Spec (.of A)) hA _ _
        hsep))
  -- The projection `g : X ×_A 𝔸ᵐ_A ⟶ X ×_A ℙᵐ_A` is a quasi-compact open immersion.
  have haS : IsOpenImmersion B (Spec (.of A)) hA (yoneda.map aP) :=
    isOpenImmersion_yoneda_map B (Spec (.of A)) hA aP
      (show AlgebraicGeometry.IsOpenImmersion aS from inferInstance)
  have hgo : IsOpenImmersion B (Spec (.of A)) hA (pullback.fst (pullback.snd
      (toBase B (Spec (.of A)) hA X).hom
      (yoneda.map (projectiveSpaceSiteObjToBase B (Spec (.of A)) hA m hP))) (yoneda.map aP)) :=
    (MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u}) Q)).of_isPullback
      (IsPullback.of_hasPullback _ _).flip haS
  have hgmono := mono_of_isOpenImmersion B (Spec (.of A)) hA _ hgo
  have haSqc : IsQuasiCompact B (Spec (.of A)) hA (yoneda.map aP) := by
    refine isQuasiCompact_of_presheaf_quasiCompact B (Spec (.of A)) hA
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B (Spec (.of A)) hA _ aP).2 ?_)
    change QuasiCompact aS
    have : QuasiCompact (aS ≫ (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))) := by
      rw [projectiveSpaceOver.affineChart_over]
      infer_instance
    exact QuasiCompact.of_comp aS (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))
  have hgqc : IsQuasiCompact B (Spec (.of A)) hA (pullback.fst (pullback.snd
      (toBase B (Spec (.of A)) hA X).hom
      (yoneda.map (projectiveSpaceSiteObjToBase B (Spec (.of A)) hA m hP))) (yoneda.map aP)) :=
    isQuasiCompact_of_isPullback B (Spec (.of A)) hA (IsPullback.of_hasPullback _ _).flip haSqc
  have hΓqc : IsQuasiCompact B (Spec (.of A)) hA (Γ' ≫ pullback.fst _ _) :=
    isQuasiCompact_comp B (Spec (.of A)) hA hTValg hTalg _ _
      (isQuasiCompact_of_isClosedImmersion' B (Spec (.of A)) hA hΓ') hgqc
  -- The scheme-theoretic image `Z` of `Γ`, and its part `W` over `𝔸ᵐ_A`.
  let Zs := schemeTheoreticImageSubfunctor B (Spec (.of A)) hA Γ
  have hZs : IsClosedSubspace B (Spec (.of A)) hA Zs :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B (Spec (.of A)) hA Γ hTalg
  have hR : Zs.preimage (pullback.fst _ (yoneda.map aP)) = Subfunctor.range Γ' := by
    have h := preimage_schemeTheoreticImageSubfunctor_comp_eq_range B (Spec (.of A)) hA hUalg
      hTalg hTValg Γ' _ hΓ' (isEtale_of_isOpenImmersion B (Spec (.of A)) hA hgo) hΓqc
    rwa [hΓ'g] at h
  -- `X ×_A ℙᵐ_A` is Noetherian.
  have hbaseN : IsNoetherian B (Spec (.of A)) hA B.contains_terminal (yoneda.obj base) :=
    ⟨isQuasiCompactSpace_yoneda_of_isAffine B (Spec (.of A)) hA base inferInstance,
      isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B (Spec (.of A)) hA (yoneda.obj base)
        B.contains_terminal ⟨base, inferInstance, ⟨Functor.RepresentableBy.yoneda base⟩⟩,
      hasEtaleLocalProperty_of_representable B (Spec (.of A)) hA _ _ base (Iso.refl _)
        (show IsLocallyNoetherian (Spec (.of A)) from inferInstance)⟩
  have hPfp : IsFinitePresentation B (Spec (.of A)) hA
      (yoneda.map (projectiveSpaceSiteObjToBase B (Spec (.of A)) hA m hP)) := by
    refine isFinitePresentation_yoneda_map B (Spec (.of A)) hA _ ?_
    change AlgebraicGeometry.FinitePresentation
      (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))
    exact ⟨(LocallyOfFinitePresentation.iff_locallyOfFiniteType).2 inferInstance, inferInstance,
      inferInstance⟩
  have hTfp : IsFinitePresentation B (Spec (.of A)) hA
      (pullback.snd (toBase B (Spec (.of A)) hA X).hom
        (yoneda.map (projectiveSpaceSiteObjToBase B (Spec (.of A)) hA m hP)) ≫
        yoneda.map (projectiveSpaceSiteObjToBase B (Spec (.of A)) hA m hP)) :=
    isFinitePresentation_comp B (Spec (.of A)) hA hTalg (isAlgebraicSpace_yoneda _ _ _ _)
      (isAlgebraicSpace_yoneda _ _ _ _) _ _
      (isFinitePresentation_pullback_snd B (Spec (.of A)) hA _ _ X.2
        (isAlgebraicSpace_yoneda _ _ _ _) (isAlgebraicSpace_yoneda _ _ _ _) hfp) hPfp
  have hTN : IsNoetherian B (Spec (.of A)) hA B.contains_terminal T.1 :=
    isNoetherian_of_isFinitePresentation B (Spec (.of A)) hA B.contains_terminal _ hTalg
      (isAlgebraicSpace_yoneda _ _ _ _) hTfp hbaseN
  -- The part of `Z` over `𝔸ᵐ_A` is `h_{U₀}`: a cartesian square.
  have hΓ'mono := mono_of_isClosedImmersion B (Spec (.of A)) hA Γ' hΓ'
  let k : yoneda.obj Z₀ ⟶ (Zs.preimage (pullback.fst _ (yoneda.map aP))).toFunctor :=
    Subfunctor.lift Γ' (le_of_eq hR.symm)
  have : IsIso k := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro c
    rw [isIso_iff_bijective]
    constructor
    · intro y₁ y₂ h
      exact (mono_iff_injective (Γ'.app c)).1 inferInstance (congrArg Subtype.val h)
    · rintro ⟨y, hy⟩
      have hy' : y ∈ (Subfunctor.range Γ').obj c := hR ▸ hy
      obtain ⟨y₀, rfl⟩ := hy'
      exact ⟨y₀, rfl⟩
  haveI : HasPullback (toBase B (Spec (.of A)) hA X).hom
      (yoneda.map (projectiveSpaceSiteObjToBase B (Spec (.of A)) hA m hP)) :=
    HasLimitsOfShape.has_limit _
  have hsqA : IsPullback (k ≫ Zs.fromPreimage _) Γ' Zs.ι (pullback.fst _ (yoneda.map aP)) :=
    IsPullback.of_iso (Subfunctor.isPullback_preimage _ Zs) (asIso k).symm (Iso.refl _)
      (Iso.refl _) (Iso.refl _) (by simp)
      (by
        rw [Iso.refl_hom, Category.comp_id]
        exact (IsIso.eq_inv_comp k).2 (Subfunctor.lift_ι _ _)) (by simp) (by simp)
  have hsq := hsqA.paste_vert (IsPullback.of_hasPullback (pullback.snd
    (toBase B (Spec (.of A)) hA X).hom
    (yoneda.map (projectiveSpaceSiteObjToBase B (Spec (.of A)) hA m hP))) (yoneda.map aP))
  rw [hΓ'snd] at hsq
  let Zsp : AlgebraicSpaces B (Spec (.of A)) hA := ⟨Zs.toFunctor, hZs.1⟩
  let i : Zsp ⟶ T := ObjectProperty.homMk Zs.ι
  let eW : yoneda.obj Z₀ ≅ (overOpen i v).1 := hsq.isoPullback
  have hsnd : (overOpenToOpen i v).hom = eW.inv ≫ yoneda.map jA := hsq.isoPullback_inv_snd.symm
  have hfst : (overOpenι i v ≫ i ≫ productFst X m hP).hom = eW.inv ≫ b := by
    rw [Iso.eq_inv_comp]
    change hsq.isoPullback.hom ≫ (pullback.fst (Zs.ι ≫ pullback.snd _ _) (yoneda.map aP) ≫
      Zs.ι ≫ pullback.fst _ _) = b
    rw [← Category.assoc, hsq.isoPullback_hom_fst, Category.assoc,
      Subfunctor.fromPreimage_ι_assoc, ← Category.assoc k, Subfunctor.lift_ι,
      ← Category.assoc, hΓ'g]
    exact pullback.lift_fst _ _ _
  have hicl : IsClosedImmersion B (Spec (.of A)) hA i.hom := hZs.2
  refine ⟨⟨m, hP, Zsp, i, hicl, ?_, V, v, haS, ?_, ?_,
    pointsMap B (Spec (.of A)) hA _ eW.hom a, ?_,
    (DerivedCategory.singleFunctor _ 0).obj (structureSheafPushforward B (Spec (.of A)) hA i),
    ⟨Iso.refl _⟩,
    isPseudoCoherent_single_structureSheafPushforward B (Spec (.of A)) hA B.contains_terminal
      hTN i hicl,
    cohomologySupportedOn_single_structureSheafPushforward B (Spec (.of A)) hA i hicl⟩, ?_, eW,
    hfst.symm, AS, Iso.refl _, jA, inferInstanceAs (IsAffine 𝔸(σ; Spec (.of A))),
    flat_affineSpace σ (Spec (.of A)), inferInstanceAs (LocallyOfFinitePresentation
      (𝔸(σ; Spec (.of A)) ↘ Spec (.of A))), hc₀, by rw [hsnd]; exact Category.comp_id _⟩
  · -- A closed immersion into a Noetherian algebraic space is of finite presentation.
    refine (isFinitePresentation_iff_isLocallyOfFinitePresentation B (Spec (.of A)) hA i
      hicl).2 ?_
    intro U' V' a' b' h ha' hb' hc
    have := isLocallyOfFiniteType_of_isClosedImmersion B (Spec (.of A)) hA _ hicl U' V' a' b'
      h ha' hb' hc
    have := isLocallyNoetherian_of_etaleChart B (Spec (.of A)) hA _ hTalg hTN.2.2 V' b' hb'
    exact (LocallyOfFinitePresentation.iff_locallyOfFiniteType).2 inferInstance
  · rw [hsnd]
    exact MorphismProperty.RespectsIso.precomp _ eW.inv _ hjA
  · rw [hfst]
    exact isEtale_comp B (Spec (.of A)) hA (isEtale_of_isIso B (Spec (.of A)) hA eW.inv)
      (isEtale_of_presheaf_etale B (Spec (.of A)) hA hb)
  · rw [← Function.comp_apply (f := pointsMap B (Spec (.of A)) hA _ _),
      ← pointsMap_comp, hfst, ← Category.assoc, eW.hom_inv_id, Category.id_comp]
  · -- Tor independence: `W ⟶ X ×_A 𝔸ᵐ_A` is the graph of `c₀` over the chart `b`.
    intro Ys Y' κ πY hY
    have hBs : IsPullback ((productOverι X m hP v ≫ productFst X m hP) : TV ⟶ X).hom
        (pullback.snd _ _ : TV.1 ⟶ yoneda.obj AS)
        ((isTerminal_yoneda_obj_base B (Spec (.of A)) hA).from X.1)
        (yoneda.map (Over.homMk AS.hom : AS ⟶ Over.mk (𝟙 (B.obj hA)))) := by
      have h := (IsPullback.of_hasPullback (pullback.snd (toBase B (Spec (.of A)) hA X).hom
        (yoneda.map (projectiveSpaceSiteObjToBase B (Spec (.of A)) hA m hP)))
          (yoneda.map aP)).paste_horiz (IsPullback.of_hasPullback
            (toBase B (Spec (.of A)) hA X).hom
            (yoneda.map (projectiveSpaceSiteObjToBase B (Spec (.of A)) hA m hP)))
      rw [← show yoneda.map aP ≫ yoneda.map (projectiveSpaceSiteObjToBase B (Spec (.of A)) hA m hP)
        = yoneda.map (Over.homMk AS.hom : AS ⟶ Over.mk (𝟙 (B.obj hA))) from
        (isTerminal_yoneda_obj_base B (Spec (.of A)) hA).hom_ext _ _, ← hb']
      exact h
    have hiX : eW.hom ≫ (overOpenToProductOver i v).hom ≫
        ((productOverι X m hP v ≫ productFst X m hP) : TV ⟶ X).hom = b := by
      have h : (overOpenToProductOver i v).hom ≫
          ((productOverι X m hP v ≫ productFst X m hP) : TV ⟶ X).hom =
            (overOpenι i v ≫ i ≫ productFst X m hP).hom :=
        congrArg (fun k => k.hom) (overOpenToProductOver_ι_assoc i v (productFst X m hP))
      rw [h, hfst, Iso.hom_inv_id_assoc]
    have hiA :
        eW.hom ≫ (overOpenToProductOver i v).hom ≫ (pullback.snd _ _ : TV.1 ⟶ yoneda.obj AS) =
          yoneda.map jA := by
      have h : (overOpenToProductOver i v).hom ≫ (pullback.snd _ _ : TV.1 ⟶ yoneda.obj AS) =
          (overOpenToOpen i v).hom :=
        congrArg (fun k => k.hom) (overOpenToProductOver_snd i v)
      rw [h, hsnd]
      exact eW.hom_inv_id_assoc _
    have : Flat AS.hom.hom := flat_affineSpace σ (Spec (.of A))
    exact torIndependent_graph_baseChange Z₀ AS Ys b
      (isEtale_of_presheaf_etale B (Spec (.of A)) hA hb)
      jA (productOverι X m hP v ≫ productFst X m hP) (pullback.snd _ _) hBs
      (overOpenToProductOver i v) eW hiX hiA κ πY hY

/-- **Stacks 0CTR over a Noetherian ring.** Let `A` be a Noetherian ring and `X` an algebraic
space separated and of finite presentation over `A`. Every point of `X` carries a datum of the
derived Chow lemma, whose closed immersion `W ⟶ X ×_A V` is moreover Tor independent of every
base change of `X ×_A V` along a morphism of schemes to `Spec A`. -/
theorem exists_derivedChowDatum_torIndependentOverBase_of_isNoetherianRing [IsNoetherianRing A]
    (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (hsep : IsSeparated B (Spec (.of A)) hA (toBase B (Spec (.of A)) hA X).hom)
    (hfp : IsFinitePresentation B (Spec (.of A)) hA (toBase B (Spec (.of A)) hA X).hom)
    (x : points B (Spec (.of A)) hA X.1) :
    ∃ D : DerivedChowDatum X x, D.TorIndependentOverBase := by
  obtain ⟨Z₀, b, hZ₀, hb, hpt⟩ :=
    exists_affine_etale_chart_at_finite_points B (Spec (.of A)) hA X.1 X.2 (n := 1) (fun _ => x)
  obtain ⟨a, rfl⟩ := hpt 0
  obtain ⟨D, hD, -⟩ := exists_derivedChowDatum_of_chart B hA X hsep hfp b hZ₀ hb a
  exact ⟨D, hD⟩

end Noetherian

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.ProjGradedModuleQcoh.ChartLocalization
public import StacksFrontier.AlgebraicGeometry.ProjGradedModuleQcoh.ChartSections
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Module.ULift
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-coherence of the sheaf associated to a graded module

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring and `M = ⨁_{i ∈ ℤ} 𝒨 i` a graded `A`-module in the
same universe. The sheaf `M̃` of degree-zero local homogeneous fractions on `Proj A` is
quasi-coherent.

The positive-degree standard opens `D₊(f)` cover `Proj A`, and each is the affine scheme
`Spec A₍f₎`. On that chart the sections of `M̃` over the standard open of a degree-zero
fraction `q` are the localization of the global chart sections at `q`, which is exactly the
condition for the chart restriction to be the sheaf associated to its module of global
sections; a module sheaf of that form on an affine scheme has a presentation. Transporting
those presentations back along the chart isomorphisms gives the local presentations that
quasi-coherence asks for.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.presentationOver`: a presentation of the
  restriction of a module to an open subscheme gives a presentation of its sections there.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.presentationOfIsLocalizing`: a localizing module
  sheaf on an affine scheme has a presentation.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.presentationOverBasicOpen`: the presentation over
  a positive-degree standard open.

## Main results

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheaf_chart_isLocalized`: on the
  chart `Spec A₍f₎`, restriction to the standard open of `q` is a localization at `q`.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheaf_isQuasicoherent`: `M̃` is
  quasi-coherent.

## Implementation notes

The generic statements about presentations are kept in their own section, where the
reducibility of sheaves on a space is left alone: the instances that recognise an isomorphism
or a colimit-preserving functor are indexed on the unmodified head symbols, and are supplied
by hand because the arguments they constrain are only determined late in elaboration.

`AlgebraicGeometry.Proj.awayι` is the chart map, and the chart's standard opens are indexed by
the degree-zero fractions `a / f ^ n`; for such a fraction the corresponding open of `Proj` is
`D₊(a * f)`, which is where the localization statement of Tag 01M4 applies.

## References

* [Stacks Project, Tag 01MB](https://stacks.math.columbia.edu/tag/01MB)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite TopCat DirectSum Stacks.GradedLocalization
open AlgebraicGeometry

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

section Presentations

/-- A presentation of the restriction of a module to an open subscheme gives a presentation of
its sections over that open. -/
public noncomputable def presentationOver {X : Scheme.{u}} (N : X.Modules) (U : X.Opens)
    (P : (N.restrict U.ι).Presentation) : (N.over U).Presentation := by
  have hpc : Limits.PreservesColimitsOfSize.{u, u} (Scheme.Modules.overEquiv U).inverse :=
    inferInstance
  have hP : ((Scheme.Modules.overEquiv U).inverse.obj (N.restrict U.ι)).Presentation :=
    @SheafOfModules.Presentation.map _ _ _ _ _ _ _ _ _ _ _ _ _ P
      (Scheme.Modules.overEquiv U).inverse hpc
      (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm
  have hiso : IsIso (((Scheme.Modules.overEquiv U).inverse.mapIso
        ((Scheme.Modules.overFunctorEquiv U).app N).symm ≪≫
      ((Scheme.Modules.overEquiv U).unitIso.app (N.over U)).symm).hom) := inferInstance
  exact @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ _ hiso hP

/-- An isomorphism of schemes over an open subscheme identifies the two restrictions. -/
public noncomputable def restrictIsoOfIsoOver {X Y : Scheme.{u}} (N : X.Modules)
    (i : Y ⟶ X) [IsOpenImmersion i] (U : X.Opens) (e : (U : Scheme.{u}) ≅ Y)
    (he : e.hom ≫ i = U.ι) : (N.restrict i).restrict e.hom ≅ N.restrict U.ι :=
  ((Scheme.Modules.restrictFunctorComp e.hom i).app N).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr he).app N

/-- A localizing module sheaf on an affine scheme has a presentation. -/
public noncomputable def presentationOfIsLocalizing {R : CommRingCat.{u}}
    (N : (Spec R).Modules) (h : IsLocalizing (modulesSpecToSheaf.obj N)) : N.Presentation := by
  have hiso : IsIso N.fromTildeΓ := (isIso_fromTildeΓ_iff_isLocalizing N).mpr h
  exact @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _
    (Scheme.Modules.fromTildeΓ N) hiso
    (presentationTilde _ Set.univ (by simp) _ (Submodule.span_eq _))

end Presentations

section ProjGraded

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local implicit_reducible] PresheafOfModules.presheaf SheafOfModules.toSheaf
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

universe v w t r

variable {S M : Type u} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ)
  [SetLike.GradedSMul 𝒜 𝒨]

section

variable [Decomposition 𝒨]

/-- The image in `Proj` of the chart standard open cut out by `a / f ^ n`. -/
public lemma awayι_image_basicOpen_mk {f : S} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (n : ℕ) (a : S) (ha : a ∈ 𝒜 (n • d))
    (hg : a * f ∈ 𝒜 (n * d + d)) (he : 0 < n * d + d)
    (hfg : AlgebraicGeometry.Proj.basicOpen 𝒜 (a * f) ≤
      AlgebraicGeometry.Proj.basicOpen 𝒜 f) :
    (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd) ''ᵁ
        PrimeSpectrum.basicOpen (HomogeneousLocalization.Away.mk 𝒜 hf n a ha) =
      AlgebraicGeometry.Proj.basicOpen 𝒜 (a * f) := by
  have hV : PrimeSpectrum.basicOpen (HomogeneousLocalization.Away.mk 𝒜 hf n a ha) =
      (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd) ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen 𝒜 (a * f) := by
    rw [AlgebraicGeometry.Proj.awayι_preimage_basicOpen 𝒜 hf hd hg he,
      ProjectiveSpectrum.isLocalizationElem_eq_pow 𝒜 hf n a ha hg,
      PrimeSpectrum.basicOpen_pow _ d hd]
  calc
    _ = (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd) ''ᵁ
        (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd) ⁻¹ᵁ
          AlgebraicGeometry.Proj.basicOpen 𝒜 (a * f) := by rw [hV]
    _ = (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd).opensRange ⊓
          AlgebraicGeometry.Proj.basicOpen 𝒜 (a * f) :=
          Scheme.Hom.image_preimage_eq_opensRange_inf _ _
    _ = AlgebraicGeometry.Proj.basicOpen 𝒜 (a * f) := by
          rw [AlgebraicGeometry.Proj.opensRange_awayι]
          exact inf_eq_right.mpr hfg

/-- On the affine chart `Spec S₍f₎`, restriction to the standard open of `a / f ^ n` exhibits
the sections there as the localization at `a / f ^ n`. -/
public lemma associatedModuleSheaf_chart_isLocalized_mk {f : S} {d : ℕ}
    (hf : f ∈ 𝒜 d) (hd : 0 < d) (n : ℕ) (a : S) (ha : a ∈ 𝒜 (n • d)) :
    IsLocalizedModule.Away (HomogeneousLocalization.Away.mk 𝒜 hf n a ha)
      ((modulesSpecToSheaf.obj ((show (AlgebraicGeometry.Proj 𝒜).Modules from
        associatedModuleSheaf 𝒜 𝒨).restrict
        (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd))).obj.map
        (PrimeSpectrum.basicOpen
          (HomogeneousLocalization.Away.mk 𝒜 hf n a ha)).leTop.op).hom := by
  have hg : a * f ∈ 𝒜 (n * d + d) := by
    simpa [smul_eq_mul] using SetLike.mul_mem_graded ha hf
  have he : 0 < n * d + d := Nat.lt_of_lt_of_le hd (Nat.le_add_left d _)
  have hfg : AlgebraicGeometry.Proj.basicOpen 𝒜 (a * f) ≤
      AlgebraicGeometry.Proj.basicOpen 𝒜 f :=
    AlgebraicGeometry.Proj.basicOpen_mono 𝒜 f (a * f) ⟨a, mul_comm a f⟩
  have himage := awayι_image_basicOpen_mk 𝒜 hf hd n a ha hg he hfg
  let φ₀ := ProjectiveSpectrum.degreeZeroRingMap 𝒜 f (a * f)
    ⟨d, hd, hf⟩ ⟨n * d + d, he, hg⟩ hfg
  let : Algebra (HomogeneousLocalization.Away 𝒜 f)
      (HomogeneousLocalization.Away 𝒜 (a * f)) := φ₀.toRingHom.toAlgebra
  let := Module.compHom (R := HomogeneousLocalization.Away 𝒜 (a * f))
    (GradedModuleDegreeZeroLocalization 𝒜 𝒨 (a * f)) φ₀.toRingHom
  let maps := ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 f (a * f)
    ⟨d, hd, hf⟩ ⟨n * d + d, he, hg⟩ hfg
  have hloc : IsLocalizedModule.Away (HomogeneousLocalization.Away.mk 𝒜 hf n a ha)
      maps.degreeZeroMap :=
    ProjectiveSpectrum.isLocalizedModule_degreeZeroMap_of_pow 𝒜 𝒨 f (a * f) d (n * d + d)
      hd he hf hg hfg _ (ProjectiveSpectrum.isLocalizationElem_eq_pow 𝒜 hf n a ha hg)
  let N : (AlgebraicGeometry.Proj 𝒜).Modules := associatedModuleSheaf 𝒜 𝒨
  let i := AlgebraicGeometry.Proj.awayι 𝒜 f hf hd
  have htop : i ''ᵁ ⊤ = AlgebraicGeometry.Proj.basicOpen 𝒜 f := by
    rw [Scheme.Hom.image_top_eq_opensRange, AlgebraicGeometry.Proj.opensRange_awayι]
  let V : (Spec (.of (HomogeneousLocalization.Away 𝒜 f))).Opens :=
    PrimeSpectrum.basicOpen (HomogeneousLocalization.Away.mk 𝒜 hf n a ha)
  let Etop := chartDegreeZeroEquiv 𝒜 𝒨 hf hd hf hd le_rfl ⊤ htop (RingHom.id _) (by simp)
  let EV := chartDegreeZeroEquiv 𝒜 𝒨 hf hd hg he hfg V himage φ₀.toRingHom
    (ProjectiveSpectrum.awayToSection_degreeZeroRingMap 𝒜 f (a * f)
      ⟨d, hd, hf⟩ ⟨n * d + d, he, hg⟩ hfg)
  let Q := modulesSpecToSheaf.obj (N.restrict i)
  let ψ := (Q.obj.map V.leTop.op).hom
  have hψ : ψ = EV.symm.toLinearMap ∘ₗ maps.degreeZeroMap ∘ₗ Etop.toLinearMap := by
    ext x
    apply EV.injective
    change EV (ψ x) = EV (EV.symm (maps.degreeZeroMap (Etop x)))
    rw [EV.apply_symm_apply]
    change (associatedModuleSheafStandardOpenEquiv 𝒜 𝒨 hg he)
        ((imageSectionsIso i N V (AlgebraicGeometry.Proj.basicOpen 𝒜 (a * f)) himage).hom
          ((N.restrict i).presheaf.map V.leTop.op x)) =
      maps.degreeZeroMap ((associatedModuleSheafStandardOpenEquiv 𝒜 𝒨 hf hd)
        ((imageSectionsIso i N ⊤ (AlgebraicGeometry.Proj.basicOpen 𝒜 f) htop).hom x))
    have hn := congrArg (fun k => k.hom x)
      (imageSectionsIso_naturality i N ⊤ V (AlgebraicGeometry.Proj.basicOpen 𝒜 f)
        (AlgebraicGeometry.Proj.basicOpen 𝒜 (a * f)) htop himage le_top hfg)
    change (imageSectionsIso i N V (AlgebraicGeometry.Proj.basicOpen 𝒜 (a * f)) himage).hom
        ((N.restrict i).presheaf.map V.leTop.op x) =
      N.presheaf.map (homOfLE hfg).op
        ((imageSectionsIso i N ⊤ (AlgebraicGeometry.Proj.basicOpen 𝒜 f) htop).hom x) at hn
    rw [hn]
    exact standardOpenEquiv_restrict 𝒜 𝒨 hf hd hg he hfg _
  change IsLocalizedModule.Away (HomogeneousLocalization.Away.mk 𝒜 hf n a ha) ψ
  rw [hψ]
  let := hloc
  exact IsLocalizedModule.of_linearEquiv _ _ EV.symm

/-- On the affine chart `Spec S₍f₎`, restriction to any standard open exhibits the sections
there as the localization at the corresponding degree-zero fraction. -/
public lemma associatedModuleSheaf_chart_isLocalized {f : S} {d : ℕ}
    (hf : f ∈ 𝒜 d) (hd : 0 < d) (q : HomogeneousLocalization.Away 𝒜 f) :
    IsLocalizedModule.Away q
      ((modulesSpecToSheaf.obj ((show (AlgebraicGeometry.Proj 𝒜).Modules from
        associatedModuleSheaf 𝒜 𝒨).restrict
        (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd))).obj.map
        (PrimeSpectrum.basicOpen q).leTop.op).hom := by
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hf q
  exact associatedModuleSheaf_chart_isLocalized_mk 𝒜 𝒨 hf hd n a ha

/-- The sections of the associated module sheaf over a positive-degree standard open have a
presentation, because that standard open is the affine chart `Spec S₍f₎`. -/
public noncomputable def presentationOverBasicOpen {f : S} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    ((show (AlgebraicGeometry.Proj 𝒜).Modules from associatedModuleSheaf 𝒜 𝒨).over
      (AlgebraicGeometry.Proj.basicOpen 𝒜 f)).Presentation := by
  have hι : (AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 f hf hd).hom ≫
      AlgebraicGeometry.Proj.awayι 𝒜 f hf hd =
      (AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι := by
    simp [AlgebraicGeometry.Proj.awayι]
  have hiso : IsIso (restrictIsoOfIsoOver
      (show (AlgebraicGeometry.Proj 𝒜).Modules from associatedModuleSheaf 𝒜 𝒨)
      (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd)
      (AlgebraicGeometry.Proj.basicOpen 𝒜 f)
      (AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 f hf hd) hι).hom := inferInstance
  exact presentationOver _ _
    (@SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ _ hiso
      (Scheme.Modules.presentationRestrict
        (AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 f hf hd).hom
        (presentationOfIsLocalizing _
          (fun q => associatedModuleSheaf_chart_isLocalized 𝒜 𝒨 hf hd q))))

/-- The sheaf of degree-zero local homogeneous fractions of a graded module on its projective
spectrum is quasi-coherent. -/
@[stacks 01MB "associated graded-module sheaves are quasi-coherent",
  ega "II 3.2.1" "affine base",
  ega "II 3.2.2" "affine base Y"]
public instance associatedModuleSheaf_isQuasicoherent :
    SheafOfModules.IsQuasicoherent.{u, u, u} (associatedModuleSheaf 𝒜 𝒨) := by
  classical
  let N : (AlgebraicGeometry.Proj 𝒜).Modules := associatedModuleSheaf 𝒜 𝒨
  apply SheafOfModules.QuasicoherentData.isQuasicoherent
  refine { I := Σ n : PNat, 𝒜 n
           X := fun j => AlgebraicGeometry.Proj.basicOpen 𝒜 (j.2 : S)
           coversTop := ?_
           presentation := ?_ }
  · refine (_root_.Opens.coversTop_iff _ _).mpr ?_
    refine TopologicalSpace.IsOpenCover.mk ?_
    refine AlgebraicGeometry.Proj.iSup_basicOpen_eq_top 𝒜
      (fun j : Σ n : PNat, 𝒜 n => (j.2 : S)) ?_
    intro z hz
    rw [← DirectSum.sum_support_decompose 𝒜 z]
    refine Ideal.sum_mem _ fun c hc => if hc0 : c = 0 then ?_ else
      Ideal.subset_span ⟨⟨⟨c, Nat.pos_iff_ne_zero.mpr hc0⟩, _⟩, rfl⟩
    convert! Ideal.zero_mem _
    subst hc0
    exact hz
  · exact fun j => presentationOverBasicOpen 𝒜 𝒨 j.2.2 j.1.2

end

end ProjGraded

end AlgebraicGeometry.ProjectiveSpectrum.Proj

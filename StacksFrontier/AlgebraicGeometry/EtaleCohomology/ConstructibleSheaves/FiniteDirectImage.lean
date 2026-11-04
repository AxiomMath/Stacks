module

public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Reduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.EtaleModuleFunctoriality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceThickening
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IntegralModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ImmersionCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.BaseChangeDecomposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral
public import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.Reduction
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
import StacksCore.Tactic.StacksAttribute

/-!
# The direct image along a finite morphism preserves constructibility

**Stacks 095R** for sheaves of modules over a Noetherian ring `Λ : Type`, on Mathlib's small
étale site, for a finite morphism of finite presentation `f : X ⟶ Y` of a big étale site `B`
with `Y` quasi-compact and quasi-separated: if `ℱ` is a constructible sheaf of `Λ`-modules on
`X_étale`, so is `f_*ℱ` on `Y_étale`.

The proof is the source's. Over an affine `Y`, Stacks 095K (2) gives a finite partition of `Y` into
affine constructible locally closed strata `Sᵢ` and finite locally free surjections `S'ᵢ ⟶ Sᵢ`
over which the reduction of `f` becomes a trivial covering `∐ₘ (S'ᵢ)_red ⟶ (S'ᵢ)_red`.
Constructibility may be checked on the strata (Stacks 09YR), and descends along `S'ᵢ ⟶ Sᵢ`
(Stacks 095Q); finite direct image commutes with base change (Stacks 0959); a thickening induces
an equivalence of étale topoi (Stacks 04DZ), so the direct image along it preserves
constructibility; and the trivial covering is finite étale, where this is Stacks 095H. A
quasi-compact and quasi-separated `Y` is covered by finitely many affine opens, and Stacks 09YR
applies again.

## Main results

* `Stacks.EtaleCohomology.isConstructibleEtaleModule_directImage_of_universalHomeomorphism`.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_directImage_of_isFinite_of_isAffine`.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_directImage_of_isFinite`.

## References

* [Stacks Project, Tag 095R](https://stacks.math.columbia.edu/tag/095R)
* [Stacks Project, Tag 095K](https://stacks.math.columbia.edu/tag/095K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring
  etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (B : BigEtaleSite.{u}) (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ]

/-- **Direct image along a universal homeomorphism preserves constructibility.** For a universal
homeomorphism `ι : Z ⟶ W` of `B` with `W` quasi-compact and quasi-separated, if `H` is a
constructible sheaf of `Λ`-modules on `Z_étale`, then `ι_*H` is constructible. -/
theorem isConstructibleEtaleModule_directImage_of_universalHomeomorphism {Z W : B.Scheme}
    (ι : Z ⟶ W) [UniversalHomeomorphism (B.inclusion.map ι)] [CompactSpace W.obj]
    [QuasiSeparatedSpace W.obj] {H : EtaleModules.{u, 0} Λ Z.obj}
    (hH : IsBigSiteConstructibleEtaleModule B Z Λ H) :
    IsBigSiteConstructibleEtaleModule B W Λ
      ((etaleModuleDirectImage.{u, 0} Λ (B.inclusion.map ι)).obj H) := by
  obtain ⟨hint, -, hsurj⟩ :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective
      (B.inclusion.map ι)).1 inferInstance
  have : IsIntegralHom (B.inclusion.map ι) := hint
  have : CompactSpace (B.inclusion.obj W) := ‹CompactSpace W.obj›
  have : QuasiSeparatedSpace (B.inclusion.obj W) := ‹QuasiSeparatedSpace W.obj›
  have : CompactSpace Z.obj := QuasiCompact.compactSpace_of_compactSpace (B.inclusion.map ι)
  have : QuasiSeparatedSpace Z.obj := quasiSeparatedSpace_of_quasiSeparated (B.inclusion.map ι)
  have := etaleModuleDirectImage_isEquivalence_of_universalHomeomorphism Λ (B.inclusion.map ι)
  refine isConstructibleEtaleModule_of_inverseImage B Λ ι hsurj.surj ?_
  exact IsBigSiteConstructibleEtaleModule.of_iso B Λ
    (asIso ((etaleModuleInverseImageAdj.{u, 0} Λ (B.inclusion.map ι)).counit.app H)).symm hH

/-- **Direct image along a map whose reduction is a trivial covering.** Let `p : P ⟶ S'` be a
morphism of `B` with `S'` quasi-compact and quasi-separated whose reduction is a trivial covering
`∐ₘ S'_red ⟶ S'_red`. Then `p_*` preserves constructibility. -/
theorem isConstructibleEtaleModule_directImage_of_reduction_trivialCovering {P S' : B.Scheme}
    (p : P.obj ⟶ S'.obj) [CompactSpace S'.obj] [QuasiSeparatedSpace S'.obj] (m : ℕ)
    (q : P.obj.nilradical.subscheme ⟶ S'.obj.nilradical.subscheme)
    (e : P.obj.nilradical.subscheme ≅ ∐ (fun _ : Fin m ↦ S'.obj.nilradical.subscheme))
    (hq : q ≫ S'.obj.nilradical.subschemeι = P.obj.nilradical.subschemeι ≫ p)
    (he : e.hom ≫ Sigma.desc (fun _ : Fin m ↦ 𝟙 S'.obj.nilradical.subscheme) = q)
    {G : EtaleModules.{u, 0} Λ P.obj} (hG : IsBigSiteConstructibleEtaleModule B P Λ G) :
    IsBigSiteConstructibleEtaleModule B S' Λ ((etaleModuleDirectImage.{u, 0} Λ p).obj G) := by
  have hPr : B.Contains P.obj.nilradical.subscheme :=
    Scheme.size_lt_of_isClosedImmersion P.obj.nilradical.subschemeι P.property
  have hSr : B.Contains S'.obj.nilradical.subscheme :=
    Scheme.size_lt_of_isClosedImmersion S'.obj.nilradical.subschemeι S'.property
  have hC : B.Contains (∐ (fun _ : Fin m ↦ S'.obj.nilradical.subscheme)) :=
    Scheme.size_lt_of_isOpenImmersion e.inv hPr
  let PrB := B.obj _ hPr
  let SrB := B.obj _ hSr
  let CB := B.obj _ hC
  let ιPB : PrB ⟶ P := ObjectProperty.homMk P.obj.nilradical.subschemeι
  let ιSB : SrB ⟶ S' := ObjectProperty.homMk S'.obj.nilradical.subschemeι
  let eB : PrB ⟶ CB := ObjectProperty.homMk e.hom
  let dB : CB ⟶ SrB := ObjectProperty.homMk (Sigma.desc (fun _ : Fin m ↦ 𝟙 _))
  let G' := (etaleModuleInverseImage.{u, 0} Λ P.obj.nilradical.subschemeι).obj G
  have := AlgebraicGeometry.universalHomeomorphism_nilradical_subschemeι P.obj
  have := AlgebraicGeometry.universalHomeomorphism_nilradical_subschemeι S'.obj
  have := etaleModuleInverseImage_isEquivalence_of_universalHomeomorphism Λ
    P.obj.nilradical.subschemeι
  let c₁ := (etaleModuleDirectImage.{u, 0} Λ p).mapIso
      (asIso ((etaleModuleInverseImageAdj.{u, 0} Λ P.obj.nilradical.subschemeι).unit.app G)) ≪≫
    (etaleModuleDirectImageComp.{u, 0} Λ P.obj.nilradical.subschemeι p _ rfl).app G'
  refine IsBigSiteConstructibleEtaleModule.of_iso B Λ c₁.symm ?_
  have hcomp : P.obj.nilradical.subschemeι ≫ p =
      (e.hom ≫ Sigma.desc (fun _ : Fin m ↦ 𝟙 S'.obj.nilradical.subscheme)) ≫
        S'.obj.nilradical.subschemeι := by
    rw [he, hq]
  let c₂ :=
    ((etaleModuleDirectImageComp.{u, 0} Λ _ S'.obj.nilradical.subschemeι _ hcomp).app G').symm ≪≫
      (etaleModuleDirectImage.{u, 0} Λ S'.obj.nilradical.subschemeι).mapIso
        ((etaleModuleDirectImageComp.{u, 0} Λ e.hom (Sigma.desc (fun _ : Fin m ↦ 𝟙 _)) _
          rfl).app G').symm
  refine IsBigSiteConstructibleEtaleModule.of_iso B Λ c₂.symm ?_
  have : IsFinite (B.inclusion.map eB) := inferInstanceAs (IsFinite e.hom)
  have : Etale (B.inclusion.map eB) := inferInstanceAs (Etale e.hom)
  have : IsFinite (B.inclusion.map dB) :=
    inferInstanceAs (IsFinite (Sigma.desc (fun _ : Fin m ↦ 𝟙 S'.obj.nilradical.subscheme)))
  have : Etale (B.inclusion.map dB) := by
    have : IsZariskiLocalAtSource (@Etale : MorphismProperty Scheme.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Etale)
    exact IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  have : UniversalHomeomorphism (B.inclusion.map ιSB) :=
    inferInstanceAs (UniversalHomeomorphism S'.obj.nilradical.subschemeι)
  exact isConstructibleEtaleModule_directImage_of_universalHomeomorphism B Λ ιSB
    (isConstructibleEtaleModule_directImage_of_finite_of_etale B Λ dB
      (isConstructibleEtaleModule_directImage_of_finite_of_etale B Λ eB
        (isConstructibleEtaleModule_inverseImage B Λ ιPB hG)))

/-- Constructibility of `t⁻¹ f_* ℱ` for `f` integral follows from that of `snd_* fst⁻¹ ℱ` on the
base change `snd : X ×_Y T ⟶ T`. -/
private theorem isConstructibleEtaleModule_inverseImage_directImage_of_pullback (R : Type)
    [CommRing R] {X Y : Scheme.{u}} {T : B.Scheme} (f₀ : X ⟶ Y) [IsIntegralHom f₀] (t : T.obj ⟶ Y)
    {F : EtaleModules.{u, 0} R X}
    (h : IsBigSiteConstructibleEtaleModule B T R
      ((etaleModuleDirectImage.{u, 0} R (pullback.snd f₀ t)).obj
        ((etaleModuleInverseImage.{u, 0} R (pullback.fst f₀ t)).obj F))) :
    IsBigSiteConstructibleEtaleModule B T R
      ((etaleModuleInverseImage.{u, 0} R t).obj
        ((etaleModuleDirectImage.{u, 0} R f₀).obj F)) := by
  have sq : IsPullback (pullback.snd f₀ t) (pullback.fst f₀ t) t f₀ :=
    (IsPullback.of_hasPullback f₀ t).flip
  have := isIso_etaleModuleBaseChange_of_isIntegralHom R f₀ _ _ _ sq
  exact IsBigSiteConstructibleEtaleModule.of_iso B R
    (asIso ((etaleModuleBaseChange.{u, 0} R f₀ _ _ _ sq.w).app F)).symm h

/-- **Finite direct image restricted to a stratum that splits after a finite locally free cover.**
Let `f : X ⟶ Y` be finite, `t : T ⟶ Y` a morphism from an affine scheme, and `g : S' ⟶ T` a
finite locally free surjection such that the reduction of the base change `P = X ×_Y S'` of `f`
is a trivial covering `∐ₘ S'_red ⟶ S'_red`. Then for every constructible `ℱ` on `X`,
`t⁻¹ f_* ℱ` is constructible. -/
theorem isConstructibleEtaleModule_inverseImage_directImage_of_split {X Y T : B.Scheme}
    (f : X ⟶ Y) [IsFinite (B.inclusion.map f)] (t₀ : T.obj ⟶ Y.obj) [IsAffine T.obj]
    {F : EtaleModules.{u, 0} Λ X.obj} (hF : IsBigSiteConstructibleEtaleModule B X Λ F)
    (S' : Scheme.{u}) (g : S' ⟶ T.obj) (hgs : Surjective g)
    (hgf : Stacks.Morphisms.IsFiniteLocallyFree g) (m : ℕ)
    (q : (pullback (B.inclusion.map f) (g ≫ t₀)).nilradical.subscheme ⟶
      S'.nilradical.subscheme)
    (e : (pullback (B.inclusion.map f) (g ≫ t₀)).nilradical.subscheme ≅
      ∐ (fun _ : Fin m ↦ S'.nilradical.subscheme))
    (hq : q ≫ S'.nilradical.subschemeι =
      (pullback (B.inclusion.map f) (g ≫ t₀)).nilradical.subschemeι ≫
        pullback.snd _ _)
    (he : e.hom ≫ Sigma.desc (fun _ : Fin m ↦ 𝟙 S'.nilradical.subscheme) = q) :
    IsBigSiteConstructibleEtaleModule B T Λ
      ((etaleModuleInverseImage.{u, 0} Λ t₀).obj
        ((etaleModuleDirectImage.{u, 0} Λ (B.inclusion.map f)).obj F)) := by
  let f₀ := B.inclusion.map f
  have : IsFinite g :=
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation g).1
      hgf).1
  have hS' : B.Contains S' := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact g T.property
  have : IsAffine S' := isAffine_of_isAffineHom g
  have hP : B.Contains (pullback f₀ (g ≫ t₀)) := Scheme.size_pullback_lt _ _ X.property hS'
  let S'B := B.obj S' hS'
  let PB := B.obj _ hP
  let gB : S'B ⟶ T := ObjectProperty.homMk g
  let fstB : PB ⟶ X := ObjectProperty.homMk (pullback.fst f₀ (g ≫ t₀))
  have : CompactSpace S'B.obj := inferInstanceAs (CompactSpace S')
  have : QuasiSeparatedSpace S'B.obj := inferInstanceAs (QuasiSeparatedSpace S')
  refine isConstructibleEtaleModule_of_inverseImage B Λ gB hgs.surj ?_
  -- finite direct image commutes with base change
  let e₁ := (etaleModuleInverseImageCompIso.{u, 0} Λ g t₀).app
    ((etaleModuleDirectImage.{u, 0} Λ f₀).obj F)
  refine IsBigSiteConstructibleEtaleModule.of_iso B Λ e₁ ?_
  refine isConstructibleEtaleModule_inverseImage_directImage_of_pullback B Λ f₀ (g ≫ t₀)
    (T := S'B) ?_
  exact isConstructibleEtaleModule_directImage_of_reduction_trivialCovering B Λ (P := PB)
    (S' := S'B) (pullback.snd f₀ (g ≫ t₀)) m q e hq he
    (isConstructibleEtaleModule_inverseImage B Λ fstB hF)

/-- **Finite direct image over an affine base preserves constructibility.** Let `f : X ⟶ Y` be a
finite morphism of finite presentation of `B` with `Y` affine. If `ℱ` is a constructible sheaf of
`Λ`-modules on `X_étale`, then `f_*ℱ` is constructible. -/
theorem isConstructibleEtaleModule_directImage_of_isFinite_of_isAffine {X Y : B.Scheme}
    (f : X ⟶ Y) [IsFinite (B.inclusion.map f)] [LocallyOfFinitePresentation (B.inclusion.map f)]
    [IsAffine Y.obj] {F : EtaleModules.{u, 0} Λ X.obj}
    (hF : IsBigSiteConstructibleEtaleModule B X Λ F) :
    IsBigSiteConstructibleEtaleModule B Y Λ
      ((etaleModuleDirectImage.{u, 0} Λ (B.inclusion.map f)).obj F) := by
  have : IsAffine (B.inclusion.obj Y) := ‹IsAffine Y.obj›
  have : IsAffine (B.inclusion.obj X) := isAffine_of_isAffineHom (B.inclusion.map f)
  have hfp : FinitePresentation (B.inclusion.map f) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨n, S, s, hS, -, hcover, hsplit⟩ :=
    exists_finite_affine_stratification_split_reduction (B.inclusion.map f) hfp
  have hSB : ∀ i, B.Contains (S i) := fun i => by
    have := (hS i).1
    have := (hS i).2.1
    exact Scheme.size_lt_of_mono_quasiCompact (s i) Y.property
  refine isConstructibleModuleSheaf_of_constructible_immersion_cover B Y Λ _
    (fun i => B.obj (S i) (hSB i)) (fun i => ObjectProperty.homMk (s i))
    (fun i => (hS i).2.1) (fun i => (hS i).2.2.2) hcover.symm (fun i => ?_)
  refine isConstructibleModuleSheaf_congr B Λ _
    (etaleModulesToSmallEtalePullbackIso B Λ
      (ObjectProperty.homMk (s i) : B.obj (S i) (hSB i) ⟶ Y) _) ?_
  have : IsAffine (B.obj (S i) (hSB i)).obj := (hS i).1
  obtain ⟨S', g, hg, hfree, m, q, e, hq, he⟩ := hsplit i
  exact isConstructibleEtaleModule_inverseImage_directImage_of_split B Λ f
    (T := B.obj (S i) (hSB i)) (s i) hF S' g hg hfree m q e hq he

/-- **Finite direct image preserves constructibility.** Let `Λ : Type` be a Noetherian ring and
`f : X ⟶ Y` a finite morphism of finite presentation of `B`. If `ℱ` is a constructible sheaf of
`Λ`-modules on Mathlib's small étale site of `X`, then `f_*ℱ` is constructible. -/
@[stacks 095R "sheaves of Λ-modules, Λ a Noetherian ring in Type, on Mathlib's small étale site
(IsBigSiteConstructibleEtaleModule); f finite and of finite presentation, no hypothesis on X or Y"]
theorem isConstructibleEtaleModule_directImage_of_isFinite {X Y : B.Scheme} (f : X ⟶ Y)
    [IsFinite (B.inclusion.map f)] [LocallyOfFinitePresentation (B.inclusion.map f)]
    {F : EtaleModules.{u, 0} Λ X.obj} (hF : IsBigSiteConstructibleEtaleModule B X Λ F) :
    IsBigSiteConstructibleEtaleModule B Y Λ
      ((etaleModuleDirectImage.{u, 0} Λ (B.inclusion.map f)).obj F) := by
  let f₀ := B.inclusion.map f
  have hU : ∀ U : (B.inclusion.obj Y).affineOpens, B.Contains U.1 := fun U =>
    Scheme.size_lt_of_isOpenImmersion U.1.ι Y.property
  refine isConstructibleModuleSheaf_of_openCover B Λ Y _
    (fun U : (B.inclusion.obj Y).affineOpens => B.obj U.1 (hU U))
    (fun U => ObjectProperty.homMk U.1.ι) (fun U => inferInstanceAs (IsOpenImmersion U.1.ι)) ?_
    (fun U => ?_)
  · refine (Set.eq_univ_of_forall fun y => ?_).symm
    have hy : y ∈ (⨆ U : (B.inclusion.obj Y).affineOpens, (U : (B.inclusion.obj Y).Opens)) := by
      rw [iSup_affineOpens_eq_top]
      trivial
    obtain ⟨U, hyU⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    refine Set.mem_iUnion.2 ⟨U, ?_⟩
    show y ∈ Set.range (U : (B.inclusion.obj Y).Opens).ι.base
    rw [Scheme.Opens.range_ι]
    exact hyU
  refine isConstructibleModuleSheaf_congr B Λ _
    (etaleModulesToSmallEtalePullbackIso B Λ
      (ObjectProperty.homMk U.1.ι : B.obj U.1 (hU U) ⟶ Y) _) ?_
  have hP : B.Contains (pullback f₀ U.1.ι) := Scheme.size_pullback_lt _ _ X.property (hU U)
  let PB := B.obj (pullback f₀ U.1.ι) hP
  let fU : PB ⟶ B.obj U.1 (hU U) := ObjectProperty.homMk (pullback.snd f₀ U.1.ι)
  let fstB : PB ⟶ X := ObjectProperty.homMk (pullback.fst f₀ U.1.ι)
  have : IsFinite (B.inclusion.map fU) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f₀ U.1.ι)
      (inferInstance : IsFinite f₀)
  have : LocallyOfFinitePresentation (B.inclusion.map fU) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f₀ U.1.ι)
      (inferInstance : LocallyOfFinitePresentation f₀)
  have : IsAffine (B.obj U.1 (hU U)).obj := U.2
  exact isConstructibleEtaleModule_inverseImage_directImage_of_pullback B Λ f₀ U.1.ι
    (T := B.obj U.1 (hU U))
    (isConstructibleEtaleModule_directImage_of_isFinite_of_isAffine B Λ fU
      (isConstructibleEtaleModule_inverseImage B Λ fstB hF))

end Stacks.EtaleCohomology

end

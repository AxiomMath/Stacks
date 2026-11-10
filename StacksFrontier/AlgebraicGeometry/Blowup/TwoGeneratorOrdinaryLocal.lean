module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorFreeCentreDescent
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.BlowUpFreePullbackIsoGlue
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.PullbackFreeAutRigidity
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.GlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusVectPullback
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorSupportedSections
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorNoetherianCorners
public import StacksFrontier.AlgebraicGeometry.ClosedCoverGlue.Sections

/-!
# The ordinary local case of [Stacks, Tag 0EXD]

Let `A` be a ring and `f₁, f₂ ∈ A`, and consider the almost blowup square of
[Stacks, Example 0EVH]: the centre `Z = Spec (A/(f₁,f₂))`, the modification
`X' = Proj (A[T₀,T₁]/(f₂T₀-f₁T₁))` and the exceptional line `E = 𝐏¹_Z`.  This file proves the
local case of the essential surjectivity half of [Stacks, Tag 0EXD] at the level of **ordinary**
finite locally free modules: a triple `(ℰ, 𝒢, φ)` with `ℰ` free comes from a finite locally free
module on `Spec A`, as an object of the categorical fibre product
`Vect(Z) ×_{Vect(E)} Vect(X')`.  The passage to the Frobenius colimits and the Zariski glueing
over a cover of `Spec A` by basic opens are done elsewhere.

## Main results

* `Stacks.AlmostBlowUp.bijective_appTop_exceptionalToCenter`: the global functions on the
  exceptional line are those of the centre.
* `Stacks.AlmostBlowUp.exists_opens_isIso_restrict_hom_free`: over an arbitrary ring, a finite
  locally free `𝒢` on `X'` with `𝒢|_E` free is trivialised over the preimage of an open containing
  the centre.  Over a Noetherian ring this is
  `Stacks.AlmostBlowUp.exists_opens_cover_center_isIso_restrict_hom_free`; the general case
  descends `𝒢` and the freeness of `𝒢|_E` to a Noetherian stage
  (`Stacks.AlmostBlowUp.exists_stage_modification_free`) and identifies the stage corners with the
  two-generator square over the stage subring by the coefficient base change squares.
* `Stacks.AlmostBlowUp.exists_vect_iso_of_free_center`: **the ordinary local case**, over an
  arbitrary ring, with no Noetherian hypothesis and in any characteristic.

## Implementation notes

The source chooses `α : 𝒪_{X'}^{⊕r} ⟶ 𝒢` "compatible with the given trivialisation of `𝒢|_E`" so
that the glued module `N` has the right triple on the nose.  Here that compatibility is never
tracked through the glueing: any isomorphisms `z^*N ≅ ℰ` and `b^*N ≅ 𝒢` can be corrected, because
every automorphism of the restriction of `ℰ ≅ 𝒪_Z^{⊕r}` to `E` is the restriction of an
automorphism of `ℰ` (`AlgebraicGeometry.Scheme.Modules.exists_iso_pullback_map_eq_of_iso_free`,
fed `Stacks.AlmostBlowUp.bijective_appTop_exceptionalToCenter`), and the corrected first
component makes the square of the categorical fibre product commute
(`CategoryTheory.Limits.CategoricalPullback.nonempty_iso_of_iso_of_iso`).

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

/-! ### Two generic steps -/

/-- **An object of a categorical fibre product whose two components are isomorphic to those of
another is isomorphic to it, as soon as every automorphism over the base of the first target
component is the image of an automorphism.**  The first component isomorphism is corrected by
the automorphism measuring the failure of compatibility. -/
theorem CategoryTheory.Limits.CategoricalPullback.nonempty_iso_of_iso_of_iso
    {𝒜 ℬ 𝒞 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞] {F : 𝒜 ⥤ 𝒞} {G : ℬ ⥤ 𝒞}
    {x y : CategoricalPullback F G} (u₀ : x.fst ≅ y.fst) (v : x.snd ≅ y.snd)
    (hrig : ∀ δ : F.obj y.fst ≅ F.obj y.fst, ∃ β : y.fst ≅ y.fst, F.map β.hom = δ.hom) :
    Nonempty (x ≅ y) := by
  obtain ⟨β, hβ⟩ := hrig (F.mapIso u₀.symm ≪≫ x.iso ≪≫ G.mapIso v ≪≫ y.iso.symm)
  refine ⟨CategoricalPullback.mkIso (u₀ ≪≫ β) v ?_⟩
  simp only [Iso.trans_hom, Functor.map_comp, hβ, Functor.mapIso_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp [← Functor.map_comp_assoc]

namespace AlgebraicGeometry

/-- **A finite locally free module on `X'`, free over the preimage of `U` through `α`, with `b`
invertible over `V` and `U ⊔ V = ⊤`, is the inverse image of a finite locally free module on `X`
which is free over `U`.**  This combines
`AlgebraicGeometry.exists_isFiniteLocallyFree_restrict_iso_compat_of_isIso_restrict_free`, whose
first chart is the freeness over `U`, with
`AlgebraicGeometry.nonempty_pullback_iso_of_restrictChartIso_compat`. -/
theorem exists_isFiniteLocallyFree_restrict_free_pullback_iso {X X' : Scheme.{u}} (b : X' ⟶ X)
    {U V : X.Opens} [IsIso (b ∣_ V)] {I : Type u} [Finite I] {G : X'.Modules}
    (α : _root_.SheafOfModules.free.{u} I ⟶ G) (hUV : U ⊔ V = ⊤)
    (hG : Scheme.Modules.IsFiniteLocallyFree G)
    (hα : IsIso ((Scheme.Modules.restrictFunctor (b ⁻¹ᵁ U).ι).map α)) :
    ∃ N : X.Modules, Scheme.Modules.IsFiniteLocallyFree N ∧
      Nonempty (Scheme.Modules.restrict N U.ι ≅
        _root_.SheafOfModules.free (R := U.toScheme.ringCatSheaf) I) ∧
      Nonempty ((Scheme.Modules.pullback b).obj N ≅ G) := by
  obtain ⟨N, κ, hN, hcompat⟩ :=
    exists_isFiniteLocallyFree_restrict_iso_compat_of_isIso_restrict_free b α hUV hG hα
  exact ⟨N, hN, ⟨κ ⟨false⟩⟩,
    nonempty_pullback_iso_of_restrictChartIso_compat b α hUV N hα κ hcompat⟩

/-- A functor carries `a ≫ f ≫ b` to an isomorphism when `a`, `b` are isomorphisms and it carries
`f` to one.  Stated in an arbitrary category, so that it applies to sheaves of modules on schemes,
at which `Functor.map_comp` does not rewrite. -/
private theorem isIso_map_iso_comp_comp_iso {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (P : 𝒞 ⥤ 𝒟)
    {W X Y Z : 𝒞} (a : W ≅ X) (f : X ⟶ Y) (b : Y ≅ Z) [IsIso (P.map f)] :
    IsIso (P.map (a.hom ≫ f ≫ b.hom)) := by
  rw [P.map_comp, P.map_comp]
  infer_instance

/-- **A trivialisation near a closed subset pulls back along a commutative square.**  If `c ≫ bB =
bA ≫ s`, `G` is the inverse image of `GB` along `c`, and `αB : 𝒪^{⊕I} ⟶ GB` is invertible over the
preimage under `bB` of an open `UB`, then `G` is trivialised by some `α` over the preimage under
`bA` of `s ⁻¹ᵁ UB`. -/
theorem exists_isIso_restrict_of_pullback {XA X'A XB X'B : Scheme.{u}} (bA : X'A ⟶ XA)
    (bB : X'B ⟶ XB) (c : X'A ⟶ X'B) (s : XA ⟶ XB) (h : c ≫ bB = bA ≫ s) {I : Type u}
    {G : X'A.Modules} {GB : X'B.Modules} (ι : G ≅ (Scheme.Modules.pullback c).obj GB)
    (UB : XB.Opens) (αB : _root_.SheafOfModules.free.{u} I ⟶ GB)
    (hα : IsIso ((Scheme.Modules.restrictFunctor (bB ⁻¹ᵁ UB).ι).map αB)) :
    ∃ α : _root_.SheafOfModules.free.{u} I ⟶ G,
      IsIso ((Scheme.Modules.restrictFunctor (bA ⁻¹ᵁ (s ⁻¹ᵁ UB)).ι).map α) := by
  have hU : bA ⁻¹ᵁ (s ⁻¹ᵁ UB) = c ⁻¹ᵁ (bB ⁻¹ᵁ UB) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h]
  refine ⟨(Scheme.Modules.pullbackFreeIso c I).symm.hom ≫ (Scheme.Modules.pullback c).map αB ≫
    ι.symm.hom, ?_⟩
  rw [hU]
  have : IsIso ((Scheme.Modules.restrictFunctor (c ⁻¹ᵁ (bB ⁻¹ᵁ UB)).ι).map
      ((Scheme.Modules.pullback c).map αB)) := StacksTag09NE.isIso_restrict_pullback_map c _ αB
  exact isIso_map_iso_comp_comp_iso _ _ _ _

end AlgebraicGeometry

namespace Stacks.AlmostBlowUp

attribute [local instance] MvPolynomial.gradedAlgebra

variable (A : Type u) [CommRing A] (f₁ f₂ : A)

/-- The projection of the exceptional line onto the centre is the structure morphism of the
polynomial model of the projective line over the centre ring. -/
theorem exceptionalToCenter_eq_projToSpecCoeff :
    exceptionalToCenter A f₁ f₂ =
      Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff (centerRing A f₁ f₂) 1 := by
  have h : (twoGeneratorSquare A f₁ f₂).centerMap =
      (GradedRing.projZeroRingHom' (exceptionalGrading A f₁ f₂)).comp
        (algebraMap (centerRing A f₁ f₂) (MvPolynomial (Fin 2) (centerRing A f₁ f₂))) :=
    RingHom.ext fun a => (GradedRing.projZeroRingHom'_apply_coe (exceptionalGrading A f₁ f₂)
      ⟨MvPolynomial.C a, (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
        (MvPolynomial.isHomogeneous_C _ a)⟩).symm
  unfold exceptionalToCenter Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff
  rw [h]

/-- **The global functions on the exceptional line are those of the centre.** -/
theorem bijective_appTop_exceptionalToCenter :
    Function.Bijective (exceptionalToCenter A f₁ f₂).appTop := by
  have hΓ : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of (centerRing A f₁ f₂))).inv :=
    ConcreteCategory.bijective_of_isIso _
  rw [exceptionalToCenter_eq_projToSpecCoeff]
  exact (Function.Bijective.of_comp_iff _ hΓ).mp
    (Stacks.ProjectiveSpace.Cohomology.bijective_coeffToGlobalSections (centerRing A f₁ f₂) 1)

/-- The image of the centre in `Spec A` is the zero locus of `(f₁, f₂)`. -/
theorem range_centerToBase_base :
    Set.range (centerToBase A f₁ f₂).base =
      PrimeSpectrum.zeroLocus (centerIdeal A f₁ f₂ : Set A) := by
  have hr := range_comap_of_surjective (centerRing A f₁ f₂)
    (Ideal.Quotient.mk (centerIdeal A f₁ f₂)) Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker] at hr
  rw [← hr]
  ext x
  exact ⟨fun ⟨y, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy⟩⟩

/-- **An open containing the centre covers the base together with the complement of the
centre.**  The support of the centre's ideal sheaf is the zero locus of `(f₁, f₂)`, which is the
image of the centre. -/
theorem sup_centerComplement_eq_top_of_range_subset {U : (Spec (.of A)).Opens}
    (hZU : Set.range (centerToBase A f₁ f₂).base ⊆ (U : Set _)) :
    U ⊔ centerComplement A f₁ f₂ = ⊤ := by
  refine top_le_iff.mp fun x _ => ?_
  by_cases hx : x ∈ ((centerIdealSheaf A f₁ f₂).support : Set (Spec (.of A)))
  · refine Or.inl (hZU ?_)
    rwa [coe_support_centerIdealSheaf, ← range_centerToBase_base] at hx
  · exact Or.inr hx

/-- **The ordinary local case, given the freeness of the module on the modification near the
exceptional line.**  Let `(ℰ, 𝒢, φ)` be a triple over the square of [Stacks, Example 0EVH] with
`ℰ` free of rank `r`, and suppose `𝒢` is trivialised by some `α` over the preimage of an open `U`
containing the centre.  Then the triple comes from a finite locally free module on the base. -/
theorem exists_vect_iso_of_isIso_restrict (r : ℕ)
    (Ec : (Spec (.of (centerRing A f₁ f₂))).Vect)
    (Em : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).Vect)
    (φ : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      (Scheme.Vect.pullback (exceptionalToCenter A f₁ f₂)).obj Ec ≅
        (Scheme.Vect.pullback (exceptionalToModification A f₁ f₂)).obj Em)
    (ε : Ec.obj ≅ _root_.SheafOfModules.free (ULift.{u} (Fin r)))
    (U : (Spec (.of A)).Opens)
    (hZU : Set.range (centerToBase A f₁ f₂).base ⊆ (U : Set _))
    (α : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      (_root_.SheafOfModules.free
        (R := (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).ringCatSheaf)
        (ULift.{u} (Fin r))) ⟶ Em.obj)
    (hα : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      IsIso ((Scheme.Modules.restrictFunctor (modificationToBase A f₁ f₂ ⁻¹ᵁ U).ι).map α)) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    ∃ N : (Spec (.of A)).Vect,
      Nonempty ((⟨(Scheme.Vect.pullback (centerToBase A f₁ f₂)).obj N,
          (Scheme.Vect.pullback (modificationToBase A f₁ f₂)).obj N,
          (vectPullbackSquareIso (twoGenerator_isPullback A f₁ f₂).w.symm).app N⟩ :
          CategoricalPullback (Scheme.Vect.pullback (exceptionalToCenter A f₁ f₂))
            (Scheme.Vect.pullback (exceptionalToModification A f₁ f₂))) ≅
        ⟨Ec, Em, φ⟩) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  have := isIso_modificationToBase_restrict_centerComplement A f₁ f₂
  have hcov := sup_centerComplement_eq_top_of_range_subset A f₁ f₂ hZU
  have hGflf : Scheme.Modules.IsFiniteLocallyFree Em.obj :=
    (Stacks.Modules.isFiniteLocallyFree_iff_localGenerators Em.obj).mpr Em.property
  obtain ⟨N, hN, ⟨κ⟩, ⟨v⟩⟩ :=
    exists_isFiniteLocallyFree_restrict_free_pullback_iso (modificationToBase A f₁ f₂) α hcov
      hGflf hα
  obtain ⟨u₀⟩ := nonempty_pullback_iso_free_of_range_subset (centerToBase A f₁ f₂) U hZU κ
  let Nv : (Spec (.of A)).Vect :=
    ⟨N, (Stacks.Modules.isFiniteLocallyFree_iff_localGenerators N).mp hN⟩
  refine ⟨Nv, CategoricalPullback.nonempty_iso_of_iso_of_iso
    (ObjectProperty.isoMk _ (u₀ ≪≫ ε.symm)) (ObjectProperty.isoMk _ v) fun δ => ?_⟩
  obtain ⟨β, hβ⟩ := Scheme.Modules.exists_iso_pullback_map_eq_of_iso_free
    (exceptionalToCenter A f₁ f₂) (bijective_appTop_exceptionalToCenter A f₁ f₂) ε
    ((ObjectProperty.ι _).mapIso δ)
  exact ⟨ObjectProperty.isoMk _ β, ObjectProperty.hom_ext _ hβ⟩

/-- **The stage of a module on the modification, with a trivialisation of its restriction to the
exceptional line.**  A finite locally free module on the modification over `A` whose restriction
to the exceptional line is free comes, through a cone leg of the stage system, from a finite
locally free module over some Noetherian stage whose restriction to the exceptional line over that
stage is free. -/
theorem exists_stage_modification_free (r : ℕ)
    (G : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).Modules)
    (hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G)
    (e : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      (Scheme.Modules.pullback (exceptionalToModification A f₁ f₂)).obj G ≅
        _root_.SheafOfModules.free (ULift.{u} (Fin r))) :
    ∃ (k : Over (initialIndex A)) (Gk : ((modificationStageDiagram A f₁ f₂).obj k).Modules),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} Gk ∧
      Nonempty (G ≅ (Scheme.Modules.pullback ((modificationStageCone A f₁ f₂).π.app k)).obj Gk) ∧
      Nonempty ((Scheme.Modules.pullback
          ((exceptionalToModificationStageDiagram A f₁ f₂).app k)).obj Gk ≅
        _root_.SheafOfModules.free (ULift.{u} (Fin r))) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  obtain ⟨k₀, G₀, hG₀, ⟨ι₀⟩⟩ :=
    exists_stage_isFiniteLocallyFree_pullback_iso_modification A f₁ f₂ G hG
  let F := (Scheme.Modules.pullback
    ((exceptionalToModificationStageDiagram A f₁ f₂).app k₀)).obj G₀
  let Fr := _root_.SheafOfModules.free
    (R := ((exceptionalStageDiagram A f₁ f₂).obj k₀).ringCatSheaf) (ULift.{u} (Fin r))
  have hw := (isPullback_exceptionalToModification_stageCone_π A f₁ f₂ k₀).w
  let θ : (Scheme.Modules.pullback ((exceptionalStageCone A f₁ f₂).π.app k₀)).obj F ≅
      (Scheme.Modules.pullback ((exceptionalStageCone A f₁ f₂).π.app k₀)).obj Fr :=
    (Scheme.Modules.pullbackComp ((exceptionalStageCone A f₁ f₂).π.app k₀)
        ((exceptionalToModificationStageDiagram A f₁ f₂).app k₀)).app G₀ ≪≫
      (Scheme.Modules.pullbackCongr hw).app G₀ ≪≫
      ((Scheme.Modules.pullbackComp (exceptionalToModification A f₁ f₂)
        ((modificationStageCone A f₁ f₂).π.app k₀)).app G₀).symm ≪≫
      (Scheme.Modules.pullback (exceptionalToModification A f₁ f₂)).mapIso ι₀.symm ≪≫ e ≪≫
      (Scheme.Modules.pullbackFreeIso ((exceptionalStageCone A f₁ f₂).π.app k₀) _).symm
  have : ∀ {a b : Over (initialIndex A)} (g : a ⟶ b),
      IsAffineHom ((exceptionalStageDiagram A f₁ f₂).map g) := fun g =>
    isAffineHom_baseChangeDiagram_map _ _ _ g
  have : CompactSpace (exceptionalStageOver A f₁ f₂).left :=
    Stacks.ProjAmple.compactSpace_proj_polyGrading
      (centerRing ↥(initialStage A f₁ f₂) (initialGen₁ A f₁ f₂) (initialGen₂ A f₁ f₂)) 1
  have : QuasiSeparatedSpace (exceptionalStageOver A f₁ f₂).left :=
    Stacks.AlgebraicGeometry.ProjQuasiSeparated.quasiSeparatedSpace_proj
      (exceptionalGrading ↥(initialStage A f₁ f₂)
        (initialGen₁ A f₁ f₂) (initialGen₂ A f₁ f₂))
  have : ∀ j, CompactSpace ((exceptionalStageDiagram A f₁ f₂).obj j) := fun j =>
    compactSpace_baseChangeDiagram_obj _ _ _ j
  have : ∀ j, QuasiSeparatedSpace ((exceptionalStageDiagram A f₁ f₂).obj j) := fun j =>
    quasiSeparatedSpace_baseChangeDiagram_obj _ _ _ j
  have : F.IsFinitePresentation :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.isFinitePresentation F
      (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme _ _ hG₀)
  have : Fr.IsFinitePresentation :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.isFinitePresentation Fr
      ((Stacks.Modules.isFiniteLocallyFree_iff_localGenerators Fr).mp
        (Scheme.Modules.isFiniteLocallyFree_free _))
  obtain ⟨k₁, ε, θ₁, -⟩ := Stacks.AlgebraicGeometry.ModuleLimits.exists_stage_iso_of_pullback_iso
    (exceptionalStageDiagram A f₁ f₂) (exceptionalStageCone A f₁ f₂)
    (isLimit_exceptionalStageCone A f₁ f₂) k₀ F Fr θ
  refine ⟨k₁, (Scheme.Modules.pullback ((modificationStageDiagram A f₁ f₂).map ε)).obj G₀,
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme _ _ hG₀, ⟨?_⟩, ⟨?_⟩⟩
  · exact ι₀ ≪≫
      (Scheme.Modules.pullbackCongr ((modificationStageCone A f₁ f₂).w ε)).symm.app G₀ ≪≫
      ((Scheme.Modules.pullbackComp ((modificationStageCone A f₁ f₂).π.app k₁)
        ((modificationStageDiagram A f₁ f₂).map ε)).app G₀).symm
  · exact (Scheme.Modules.pullbackComp ((exceptionalToModificationStageDiagram A f₁ f₂).app k₁)
        ((modificationStageDiagram A f₁ f₂).map ε)).app G₀ ≪≫
      (Scheme.Modules.pullbackCongr
        ((exceptionalToModificationStageDiagram A f₁ f₂).naturality ε)).symm.app G₀ ≪≫
      ((Scheme.Modules.pullbackComp ((exceptionalStageDiagram A f₁ f₂).map ε)
        ((exceptionalToModificationStageDiagram A f₁ f₂).app k₀)).app G₀).symm ≪≫ θ₁ ≪≫
      Scheme.Modules.pullbackFreeIso ((exceptionalStageDiagram A f₁ f₂).map ε) _

/-- The morphism of stage diagrams induced by the inclusion of the exceptional line, on the
second projection of the base change. -/
theorem exceptionalToModificationStageDiagram_app_snd (k : Over (initialIndex A)) :
    letI := (twoGeneratorSquare ↥(initialStage A f₁ f₂)
      (initialGen₁ A f₁ f₂) (initialGen₂ A f₁ f₂)).modificationGraded
    (exceptionalToModificationStageDiagram A f₁ f₂).app k ≫
        pullback.snd ((noetherianStageSpecDiagram A f₁ f₂).map k.hom)
          (modificationStageOver A f₁ f₂).hom =
      pullback.snd ((noetherianStageSpecDiagram A f₁ f₂).map k.hom)
          (exceptionalStageOver A f₁ f₂).hom ≫
        exceptionalToModification ↥(initialStage A f₁ f₂) (initialGen₁ A f₁ f₂)
          (initialGen₂ A f₁ f₂) :=
  baseChangeMap_snd _ _ _ _

/-- **The coefficient base change squares carry the inclusion of the exceptional line over a stage
ring to the stage component of the inclusion of the exceptional lines.** -/
theorem exceptionalToModification_comp_isoPullback_hom (k : Over (initialIndex A)) :
    letI : Algebra ↥(initialStage A f₁ f₂) ↥(noetherianStage A f₁ f₂ k.left.unop) :=
      (Subring.inclusion (monotone_noetherianStage A f₁ f₂ k.hom.unop.le)).toAlgebra
    exceptionalToModification ↥(noetherianStage A f₁ f₂ k.left.unop)
        (algebraMap ↥(initialStage A f₁ f₂) _ (initialGen₁ A f₁ f₂))
        (algebraMap ↥(initialStage A f₁ f₂) _ (initialGen₂ A f₁ f₂)) ≫
      ((isPullback_modificationToBase_coeff (initialStage A f₁ f₂)
          (noetherianStage A f₁ f₂ k.left.unop) (initialGen₁ A f₁ f₂)
          (initialGen₂ A f₁ f₂)).isoPullback :
        _ ≅ (modificationStageDiagram A f₁ f₂).obj k).hom =
    ((isPullback_exceptionalToBase_coeff (initialStage A f₁ f₂)
          (noetherianStage A f₁ f₂ k.left.unop) (initialGen₁ A f₁ f₂)
          (initialGen₂ A f₁ f₂)).isoPullback :
        _ ≅ (exceptionalStageDiagram A f₁ f₂).obj k).hom ≫
      (exceptionalToModificationStageDiagram A f₁ f₂).app k := by
  let : Algebra ↥(initialStage A f₁ f₂) ↥(noetherianStage A f₁ f₂ k.left.unop) :=
    (Subring.inclusion (monotone_noetherianStage A f₁ f₂ k.hom.unop.le)).toAlgebra
  have hM := isPullback_modificationToBase_coeff (initialStage A f₁ f₂)
      (noetherianStage A f₁ f₂ k.left.unop) (initialGen₁ A f₁ f₂) (initialGen₂ A f₁ f₂)
  have hE := isPullback_exceptionalToBase_coeff (initialStage A f₁ f₂)
      (noetherianStage A f₁ f₂ k.left.unop) (initialGen₁ A f₁ f₂) (initialGen₂ A f₁ f₂)
  let ψE : _ ≅ (exceptionalStageDiagram A f₁ f₂).obj k := hE.isoPullback
  refine pullback.hom_ext ?_ ?_
  · refine ((Category.assoc _ _ _).trans (congrArg _ hM.isoPullback_hom_fst)).trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _)
    refine Eq.trans ?_ (congrArg (fun t => ψE.hom ≫ t)
      (baseChangeMap_fst _ _ _ (exceptionalToModificationStageOver A f₁ f₂)).symm)
    refine Eq.trans ?_ hE.isoPullback_hom_fst.symm
    exact (twoGenerator_isPullback ↥(noetherianStage A f₁ f₂ k.left.unop)
      (algebraMap ↥(initialStage A f₁ f₂) _ (initialGen₁ A f₁ f₂))
      (algebraMap ↥(initialStage A f₁ f₂) _ (initialGen₂ A f₁ f₂))).w
  · have h3 := exceptionalToModificationStageDiagram_app_snd A f₁ f₂ k
    have h4 := exceptionalToModification_comp_modificationCoeffProjMap (initialStage A f₁ f₂)
      (noetherianStage A f₁ f₂ k.left.unop) (initialGen₁ A f₁ f₂) (initialGen₂ A f₁ f₂)
    refine ((Category.assoc _ _ _).trans (congrArg _ hM.isoPullback_hom_snd)).trans (h4.trans ?_)
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine Eq.trans ?_ (congrArg (fun t => ψE.hom ≫ t) h3.symm)
    refine Eq.trans ?_ (Category.assoc _ _ _)
    exact congrArg (· ≫ _) hE.isoPullback_hom_snd.symm

/-- **The cone leg of the modification, followed by the coefficient base change and the structure
morphism over a stage ring, is the structure morphism followed by the cone leg of the base.** -/
theorem modificationStageCone_π_app_comp_modificationToBase (k : Over (initialIndex A)) :
    letI : Algebra ↥(initialStage A f₁ f₂) ↥(noetherianStage A f₁ f₂ k.left.unop) :=
      (Subring.inclusion (monotone_noetherianStage A f₁ f₂ k.hom.unop.le)).toAlgebra
    ((modificationStageCone A f₁ f₂).π.app k ≫
        ((isPullback_modificationToBase_coeff (initialStage A f₁ f₂)
            (noetherianStage A f₁ f₂ k.left.unop) (initialGen₁ A f₁ f₂)
            (initialGen₂ A f₁ f₂)).isoPullback :
          _ ≅ (modificationStageDiagram A f₁ f₂).obj k).inv) ≫
      modificationToBase ↥(noetherianStage A f₁ f₂ k.left.unop)
        (algebraMap ↥(initialStage A f₁ f₂) _ (initialGen₁ A f₁ f₂))
        (algebraMap ↥(initialStage A f₁ f₂) _ (initialGen₂ A f₁ f₂)) =
    modificationToBase A f₁ f₂ ≫ (noetherianStageSpecCone A f₁ f₂).π.app k.left := by
  let : Algebra ↥(initialStage A f₁ f₂) ↥(noetherianStage A f₁ f₂ k.left.unop) :=
    (Subring.inclusion (monotone_noetherianStage A f₁ f₂ k.hom.unop.le)).toAlgebra
  refine ((Category.assoc _ _ _).trans (congrArg _ (isPullback_modificationToBase_coeff
    (initialStage A f₁ f₂) (noetherianStage A f₁ f₂ k.left.unop) (initialGen₁ A f₁ f₂)
    (initialGen₂ A f₁ f₂)).isoPullback_inv_fst)).trans ?_
  have hπ : (modificationStageCone A f₁ f₂).π.app k =
      (isPullback_modificationToBase_initialStage A f₁ f₂).isoPullback.hom ≫
        (baseChangeCone (noetherianStageSpecDiagram A f₁ f₂) (noetherianStageSpecCone A f₁ f₂)
          (initialIndex A) (modificationStageOver A f₁ f₂)).π.app k := rfl
  have hbt := baseChangeTransition_fst ((noetherianStageSpecDiagram A f₁ f₂).map k.hom)
    ((noetherianStageSpecCone A f₁ f₂).π.app (initialIndex A))
    ((noetherianStageSpecCone A f₁ f₂).π.app k.left)
    ((noetherianStageSpecCone A f₁ f₂).w k.hom) (modificationStageOver A f₁ f₂)
  rw [hπ, baseChangeCone_π_app]
  refine (Category.assoc _ _ _).trans ((congrArg _ hbt).trans ?_)
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (· ≫ (noetherianStageSpecCone A f₁ f₂).π.app k.left)
    (isPullback_modificationToBase_initialStage A f₁ f₂).isoPullback_hom_fst

/-- **The cone leg of the base sends the centre into the centre over the stage ring.** -/
theorem range_centerToBase_subset_preimage_stage (k : Over (initialIndex A)) :
    letI : Algebra ↥(initialStage A f₁ f₂) ↥(noetherianStage A f₁ f₂ k.left.unop) :=
      (Subring.inclusion (monotone_noetherianStage A f₁ f₂ k.hom.unop.le)).toAlgebra
    Set.range (centerToBase A f₁ f₂).base ⊆
      ((noetherianStageSpecCone A f₁ f₂).π.app k.left).base ⁻¹'
        Set.range (centerToBase ↥(noetherianStage A f₁ f₂ k.left.unop)
          (algebraMap ↥(initialStage A f₁ f₂) _ (initialGen₁ A f₁ f₂))
          (algebraMap ↥(initialStage A f₁ f₂) _ (initialGen₂ A f₁ f₂))).base := by
  let : Algebra ↥(initialStage A f₁ f₂) ↥(noetherianStage A f₁ f₂ k.left.unop) :=
    (Subring.inclusion (monotone_noetherianStage A f₁ f₂ k.hom.unop.le)).toAlgebra
  rintro _ ⟨y, rfl⟩
  refine (Set.ext_iff.mp (range_centerToBase_base _ _ _) _).mpr
    ((PrimeSpectrum.mem_zeroLocus _ _).mpr ?_)
  refine (Ideal.span_le (I := (PrimeSpectrum.comap (noetherianStage A f₁ f₂ k.left.unop).subtype
    (PrimeSpectrum.comap (Ideal.Quotient.mk (centerIdeal A f₁ f₂)) y)).asIdeal)).mpr ?_
  rintro _ (rfl | rfl)
  · change Ideal.Quotient.mk (centerIdeal A f₁ f₂) f₁ ∈ y.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))]
    exact y.asIdeal.zero_mem
  · change Ideal.Quotient.mk (centerIdeal A f₁ f₂) f₂ ∈ y.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))]
    exact y.asIdeal.zero_mem

/-- **A finite locally free module on the modification whose restriction to the exceptional line
is free is trivialised over the preimage of an open containing the centre**, over an arbitrary
ring.  The module and the freeness descend to a Noetherian stage
(`Stacks.AlmostBlowUp.exists_stage_modification_free`); the stage corners are the corners of the
two-generator square over the stage ring by the coefficient base change squares, where
`Stacks.AlmostBlowUp.exists_opens_cover_center_isIso_restrict_hom_free` applies, and the
trivialisation pulls back along the cone leg. -/
theorem exists_opens_isIso_restrict_hom_free (r : ℕ)
    (G : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).Modules)
    (hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G)
    (e : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      (Scheme.Modules.pullback (exceptionalToModification A f₁ f₂)).obj G ≅
        _root_.SheafOfModules.free (ULift.{u} (Fin r))) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    ∃ (U : (Spec (.of A)).Opens) (α : (_root_.SheafOfModules.free
        (R := (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).ringCatSheaf)
        (ULift.{u} (Fin r))) ⟶ G),
      Set.range (centerToBase A f₁ f₂).base ⊆ (U : Set _) ∧
        IsIso ((Scheme.Modules.restrictFunctor (modificationToBase A f₁ f₂ ⁻¹ᵁ U).ι).map α) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  obtain ⟨k, Gk, hGk, ⟨ιk⟩, ⟨ek⟩⟩ := exists_stage_modification_free A f₁ f₂ r G hG e
  let A₀ := ↥(initialStage A f₁ f₂)
  let B := ↥(noetherianStage A f₁ f₂ k.left.unop)
  have hle : initialStage A f₁ f₂ ≤ noetherianStage A f₁ f₂ k.left.unop :=
    monotone_noetherianStage A f₁ f₂ k.hom.unop.le
  let : Algebra A₀ B := (Subring.inclusion hle).toAlgebra
  let g₁ := initialGen₁ A f₁ f₂
  let g₂ := initialGen₂ A f₁ f₂
  let := (twoGeneratorSquare A₀ g₁ g₂).modificationGraded
  let := (twoGeneratorSquare B (algebraMap A₀ B g₁) (algebraMap A₀ B g₂)).modificationGraded
  have hM := isPullback_modificationToBase_coeff A₀ B g₁ g₂
  have hE := isPullback_exceptionalToBase_coeff A₀ B g₁ g₂
  let ψ : AlgebraicGeometry.Proj (modificationGrading B (algebraMap A₀ B g₁) (algebraMap A₀ B g₂)) ≅
      (modificationStageDiagram A f₁ f₂).obj k := hM.isoPullback
  let ψE : AlgebraicGeometry.Proj (exceptionalGrading B (algebraMap A₀ B g₁) (algebraMap A₀ B g₂)) ≅
      (exceptionalStageDiagram A f₁ f₂).obj k := hE.isoPullback
  have hd : exceptionalToModification B (algebraMap A₀ B g₁) (algebraMap A₀ B g₂) ≫ ψ.hom =
      ψE.hom ≫ (exceptionalToModificationStageDiagram A f₁ f₂).app k :=
    exceptionalToModification_comp_isoPullback_hom A f₁ f₂ k
  let GB := (Scheme.Modules.pullback ψ.hom).obj Gk
  have hGB : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} GB :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme _ _ hGk
  let eB : (Scheme.Modules.pullback
      (exceptionalToModification B (algebraMap A₀ B g₁) (algebraMap A₀ B g₂))).obj GB ≅
        _root_.SheafOfModules.free (ULift.{u} (Fin r)) :=
    (Scheme.Modules.pullbackComp _ ψ.hom).app Gk ≪≫ (Scheme.Modules.pullbackCongr hd).app Gk ≪≫
      ((Scheme.Modules.pullbackComp ψE.hom _).app Gk).symm ≪≫
      (Scheme.Modules.pullback ψE.hom).mapIso ek ≪≫ Scheme.Modules.pullbackFreeIso ψE.hom _
  obtain ⟨UB, αB, -, hZUB, -, hαB⟩ := exists_opens_cover_center_isIso_restrict_hom_free B
    (algebraMap A₀ B g₁) (algebraMap A₀ B g₂) r hGB eB
  let c := (modificationStageCone A f₁ f₂).π.app k ≫ ψ.inv
  let s := (noetherianStageSpecCone A f₁ f₂).π.app k.left
  have hcs : c ≫ modificationToBase B (algebraMap A₀ B g₁) (algebraMap A₀ B g₂) =
      modificationToBase A f₁ f₂ ≫ s :=
    modificationStageCone_π_app_comp_modificationToBase A f₁ f₂ k
  have hc : c ≫ ψ.hom = (modificationStageCone A f₁ f₂).π.app k :=
    (Category.assoc _ _ _).trans ((congrArg _ ψ.inv_hom_id).trans (Category.comp_id _))
  let ι : G ≅ (Scheme.Modules.pullback c).obj GB :=
    ιk ≪≫ (Scheme.Modules.pullbackCongr hc).symm.app Gk ≪≫
      ((Scheme.Modules.pullbackComp c ψ.hom).app Gk).symm
  obtain ⟨α, hα⟩ := AlgebraicGeometry.exists_isIso_restrict_of_pullback (modificationToBase A f₁ f₂)
    (modificationToBase B (algebraMap A₀ B g₁) (algebraMap A₀ B g₂)) c s hcs ι UB αB hαB
  exact ⟨s ⁻¹ᵁ UB, α, fun _ hx => hZUB (range_centerToBase_subset_preimage_stage A f₁ f₂ k hx), hα⟩

/-- **The ordinary local case of [Stacks, Tag 0EXD].**  Let `A` be an arbitrary ring and
`f₁, f₂ ∈ A`.  A triple `(ℰ, 𝒢, φ)` over the almost blowup square of [Stacks, Example 0EVH] —
a finite locally free module `ℰ` on the centre, a finite locally free module `𝒢` on the
modification and an isomorphism `φ` of their restrictions to the exceptional line — whose module
`ℰ` on the centre is free comes from a finite locally free module `N` on `Spec A`: the triple
`(z^*N, b^*N, can)` is isomorphic to it in the categorical fibre product.

No Noetherian hypothesis and no characteristic are needed.  The source's argument is followed: a
map `α : 𝒪^{⊕r} ⟶ 𝒢` invertible over the preimage of an open `U` containing the centre is
produced by the `ℐ`-adic lifting over a Noetherian stage
(`Stacks.AlmostBlowUp.exists_opens_isIso_restrict_hom_free`), `N` is glued from `𝒪_U^{⊕r}` and
from `𝒢` over the complement of the centre, and the two component isomorphisms are made
compatible with `φ` by the rigidity of automorphisms along `𝐏¹_Z ⟶ Z`
(`Stacks.AlmostBlowUp.exists_vect_iso_of_isIso_restrict`). -/
theorem exists_vect_iso_of_free_center (r : ℕ)
    (Ec : (Spec (.of (centerRing A f₁ f₂))).Vect)
    (Em : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).Vect)
    (φ : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      (Scheme.Vect.pullback (exceptionalToCenter A f₁ f₂)).obj Ec ≅
        (Scheme.Vect.pullback (exceptionalToModification A f₁ f₂)).obj Em)
    (hEc : Nonempty (Ec.obj ≅ _root_.SheafOfModules.free (ULift.{u} (Fin r)))) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    ∃ N : (Spec (.of A)).Vect,
      Nonempty ((⟨(Scheme.Vect.pullback (centerToBase A f₁ f₂)).obj N,
          (Scheme.Vect.pullback (modificationToBase A f₁ f₂)).obj N,
          (vectPullbackSquareIso (twoGenerator_isPullback A f₁ f₂).w.symm).app N⟩ :
          CategoricalPullback (Scheme.Vect.pullback (exceptionalToCenter A f₁ f₂))
            (Scheme.Vect.pullback (exceptionalToModification A f₁ f₂))) ≅
        ⟨Ec, Em, φ⟩) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  obtain ⟨ε⟩ := hEc
  let eG : (Scheme.Modules.pullback (exceptionalToModification A f₁ f₂)).obj Em.obj ≅
      _root_.SheafOfModules.free (ULift.{u} (Fin r)) :=
    (ObjectProperty.ι _).mapIso φ.symm ≪≫
      (Scheme.Modules.pullback (exceptionalToCenter A f₁ f₂)).mapIso ε ≪≫
        Scheme.Modules.pullbackFreeIso (exceptionalToCenter A f₁ f₂) _
  obtain ⟨U, α, hZU, hα⟩ := exists_opens_isIso_restrict_hom_free A f₁ f₂ r Em.obj Em.property eG
  exact exists_vect_iso_of_isIso_restrict A f₁ f₂ r Ec Em φ ε U hZU α hα

end Stacks.AlmostBlowUp

end

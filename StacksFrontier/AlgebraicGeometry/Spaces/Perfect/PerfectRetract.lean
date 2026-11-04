module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedPerfectModel
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ChartLocalPerfectness
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentKernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.Homology.Perfect.Saturation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedModulePullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PseudoCoherenceAndTorAmplitude
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DistinguishedTrianglesGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectObjects
public import StacksFrontier.CategoryTheory.Triangulated.LocallySmallCompactEnvelope
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PseudoCoherenceGeneral

/-!
# A direct summand of a perfect object of an algebraic space is perfect

Let `X` be an algebraic space and `F` a retract in `D(𝒪_X)` of a perfect object `E`. Then `F` is
perfect. This is Stacks 08GA read on the small étale ringed site of an algebraic space.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_retract`: a retract of a quasi-coherent
  module is quasi-coherent.
* `AlgebraicGeometry.Space.isPerfect_of_retract`: the statement above.

## Implementation notes

Perfectness is tested on the affine charts of a covering on which `E` has a strictly perfect
model (`AlgebraicGeometry.Space.isPerfect_of_hasStrictlyPerfectModel_chart`). On such an affine
chart, the derived sections of the pullback of `E` form a perfect complex of modules over the
ring of the chart
(`AlgebraicGeometry.Space.isPerfect_representedAffineDerivedSections_obj_of_isStrictlyPerfect`),
those of the pullback of `F` are a retract of it, hence perfect, and the pullback of `F` is the
associated object of its derived sections, which has a strictly perfect model.

## References

* [Stacks Project, Tag 08GA](https://stacks.math.columbia.edu/tag/08GA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A retract of an object satisfying a property closed under kernels and isomorphisms satisfies
it: the retract is the kernel of the complementary idempotent. -/
theorem prop_of_retract_of_isClosedUnderKernels {C : Type*} [Category C] [Preadditive C]
    (P : ObjectProperty C) [P.IsClosedUnderKernels] {M N : C} (i : M ⟶ N) (r : N ⟶ M)
    (hir : i ≫ r = 𝟙 M) (hN : P N) : P M := by
  let φ : N ⟶ N := 𝟙 N - r ≫ i
  have hw : i ≫ φ = 0 := by
    simp only [φ, Preadditive.comp_sub, Category.comp_id, ← Category.assoc, hir,
      Category.id_comp, sub_self]
  refine P.prop_of_isLimit_kernelFork (f := φ) (k := KernelFork.ofι i hw) ?_ hN hN
  refine KernelFork.IsLimit.ofι _ _ (fun g _ => g ≫ r) (fun g hg => ?_) (fun g hg m hm => ?_)
  · have : g ≫ φ = 0 := hg
    simp only [φ, Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at this
    rw [Category.assoc, ← this]
  · rw [← hm, Category.assoc, hir, Category.comp_id]

/-- **A perfect object of `D(𝒪_X)` lies in `D_QCoh(𝒪_X)`**, being pseudo-coherent. -/
theorem qcohDerived_of_isPerfect_derivedCategoryB (X : AlgebraicSpaces B S hS)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) E :=
  derivedCategoryB_of_isPseudoCoherent_unconditional B S hS X.1 X.2 E
    (RingedSite.isPseudoCoherent_of_isPerfect_general _ hE)

/-- **A retract in `D(𝒪_X)` of an object of `D_QCoh(𝒪_X)` lies in `D_QCoh(𝒪_X)`.** -/
theorem derivedCategoryB_of_retract (X : AlgebraicSpaces B S hS)
    {E F : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (i : F ⟶ E) (r : E ⟶ F) (hir : i ≫ r = 𝟙 F)
    (hE : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) E) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) F := by
  have := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS X.1 X.2
  intro n
  refine prop_of_retract_of_isClosedUnderKernels _
    ((DerivedCategory.homologyFunctor _ n).map i) ((DerivedCategory.homologyFunctor _ n).map r)
    ((Functor.map_comp _ i r).symm.trans
      ((congrArg (DerivedCategory.homologyFunctor _ n).map hir).trans
        (CategoryTheory.Functor.map_id _ _))) (hE n)

/-- A bounded complex of retracts of finite free modules is strictly perfect. -/
theorem isStrictlyPerfect_of_isRetractOfFiniteFree (Y : AlgebraicSpaces B S hS)
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ)
    (hP : ∀ j, IsRetractOfFiniteFree
      (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y)) (P.X j))
    (a b : ℤ) (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b) :
    IsStrictlyPerfect.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) P := by
  refine ⟨?_, fun j => ?_⟩
  · refine (Set.finite_Icc a b).subset fun i hi => ?_
    simp only [Set.mem_setOf_eq] at hi
    by_contra hnot
    simp only [Set.mem_Icc, not_and_or, not_le] at hnot
    rcases hnot with hlt | hlt
    · exact hi (P.isZero_of_isStrictlyGE a i hlt)
    · exact hi (P.isZero_of_isStrictlyLE b i hlt)
  · obtain ⟨n, i, r, hir⟩ := hP j
    let O₁ := SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y)
    let eb : SheafOfModules.free (R := ringedToposStructureRingSheaf B S hS Y)
        (ULift.{u} (Fin n)) ≅ ⨁ fun _ : Fin n => O₁ :=
      (Sigma.reindex Equiv.ulift.symm (fun _ : ULift.{u} (Fin n) => O₁)).symm ≪≫
        (biproduct.isoCoproduct _).symm
    exact (isDirectSummandOfFiniteFree_iff_free _ _).2
      ⟨n, i ≫ eb.inv, eb.hom ≫ r,
        ((Category.assoc _ _ _).trans (congrArg (i ≫ ·) (Iso.inv_hom_id_assoc eb r))).trans hir⟩

/-- **Stacks 08GA for algebraic spaces.** A retract in `D(𝒪_X)` of a perfect object is
perfect. -/
theorem isPerfect_of_retract (X : AlgebraicSpaces B S hS)
    {E F : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (i : F ⟶ E) (r : E ⟶ F) (hir : i ≫ r = 𝟙 F)
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) :
    RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) F := by
  have hFq :=
    derivedCategoryB_of_retract X i r hir (qcohDerived_of_isPerfect_derivedCategoryB X E hE)
  refine isPerfect_of_hasStrictlyPerfectModel_chart F fun U => ?_
  obtain ⟨R, hR, hRmod⟩ := exists_hasStrictlyPerfectModel_chart_of_isPerfect E hE U
  refine ⟨fun W _ => IsAffineChart B S hS X.1 W ∧ HasStrictlyPerfectModel B S hS
      ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X W)).obj E), ?_,
    fun W g hW => ?_⟩
  · refine (SmallEtale.topology B S hS X.1).transitive hR _ fun V f hf => ?_
    obtain ⟨V', h, g', hg', rfl⟩ := hf
    have hV : HasStrictlyPerfectModel B S hS
        ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E) :=
      (hRmod g' hg').chartRestriction h
    refine (SmallEtale.topology B S hS X.1).superset_covering ?_
      (generate_isAffineChart_mem_topology B S hS X V)
    rintro W k ⟨W', k', k'', hW', hfac⟩
    exact ⟨W', k', k'' ≫ h ≫ g', ⟨hW', hV.chartRestriction k''⟩, by
      rw [← hfac, Category.assoc]⟩
  · obtain ⟨hWa, hWmod⟩ := hW
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj W)) :=
      hWa
    let U₀ := (SmallEtale.toOver B S hS X.1).obj W
    let p := chartToSpace B S hS X W
    let L := smallEtaleDerivedModulePullback B S hS p
    let RΓ := representedAffineDerivedSections B S hS U₀
    obtain ⟨P, hP, ⟨a, b, ha, hb⟩, ⟨e⟩⟩ := hWmod
    have hSP := isStrictlyPerfect_of_isRetractOfFiniteFree (chartSpace B S hS X W) P hP a b ha hb
    have hRΓE := isPerfect_representedAffineDerivedSections_obj_of_isStrictlyPerfect
      (B := B) (S := S) (hS := hS) (U := U₀) (L.obj E) P hSP e
    have hRΓF : StacksDraft.Perfect.IsPerfect (RΓ.obj (L.obj F)) :=
      StacksDraft.Perfect.isPerfect_of_retract (RΓ.map (L.map i)) (RΓ.map (L.map r))
        ((RΓ.map_comp _ _).symm.trans ((congrArg RΓ.map ((L.map_comp i r).symm.trans
          ((congrArg L.map hir).trans (L.map_id F)))).trans (RΓ.map_id _))) hRΓE
    have hLFq := derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ p F hFq
    exact (hasStrictlyPerfectModel_representedAffineDerivedAssociated_obj B S hS U₀ _ hRΓF).of_iso
      (@asIso _ _ _ _ ((representedAffineDerivedAdjunction B S hS U₀).counit.app (L.obj F))
        (isIso_representedAffineDerivedAdjunction_counit_app B S hS U₀ (L.obj F) hLFq))

/-- Perfectness of an object of `D(𝒪_X)` is invariant under isomorphism. -/
instance perfectProperty_isClosedUnderIsomorphisms (X : AlgebraicSpaces B S hS) :
    (perfectProperty B S hS X).IsClosedUnderIsomorphisms where
  of_iso e h := RingedSite.IsPerfect.of_iso _ h e

/-- A retract of a perfect object of `D(𝒪_X)` is perfect (`isPerfect_of_retract`). -/
instance perfectProperty_isStableUnderRetracts (X : AlgebraicSpaces B S hS) :
    (perfectProperty B S hS X).IsStableUnderRetracts where
  of_retract r h := isPerfect_of_retract X r.i r.r r.retract h

/-- **Stacks 08G9 for algebraic spaces**: the perfect objects of `D(𝒪_X)` form a triangulated
subcategory. -/
instance perfectProperty_isTriangulated (X : AlgebraicSpaces B S hS) :
    (perfectProperty B S hS X).IsTriangulated where
  exists_zero := ⟨(0 : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS X))), isZero_zero _,
    isPerfect_of_retract X (0 : (0 : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS X))) ⟶ _) 0
    ((isZero_zero _).eq_of_src _ _) (isPerfect_unit X)⟩
  isStableUnderShiftBy n := ⟨fun _ h =>
    RingedSite.isPerfect_shift_general (smallEtaleRingedSite B S hS X.1 X.2) h n⟩
  ext₂' T hT h₁ h₃ := ObjectProperty.le_isoClosure _ _
    (RingedSite.isPerfect_obj₂_of_distinguished_general (smallEtaleRingedSite B S hS X.1 X.2)
      T hT h₁ h₃)

/-- **Perfectness of the image under a triangulated functor is a thick property.** For a
triangulated functor `Φ` into `D(𝒪_Y)`, the objects whose image is perfect form a triangulated
subcategory stable under retracts. -/
theorem perfectProperty_inverseImage_isTriangulated_isStableUnderRetracts
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (Y : AlgebraicSpaces B S hS)
    (Φ : C ⥤ DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    [Φ.CommShift ℤ] [Φ.IsTriangulated] :
    ((perfectProperty B S hS Y).inverseImage Φ).IsTriangulated ∧
      ((perfectProperty B S hS Y).inverseImage Φ).IsStableUnderRetracts :=
  ⟨{  exists_zero := ⟨0, isZero_zero _, isPerfect_of_retract Y (0 : Φ.obj 0 ⟶ (0 : DerivedCategory
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))) 0
          ((Φ.map_isZero (isZero_zero _)).eq_of_src _ _)
          (isPerfect_of_retract Y (0 : (0 : DerivedCategory
            (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) ⟶ _) 0
            ((isZero_zero _).eq_of_src _ _) (isPerfect_unit Y))⟩
      isStableUnderShiftBy := fun n => ⟨fun E h =>
        RingedSite.IsPerfect.of_iso _ (RingedSite.isPerfect_shift_general _ h n)
          ((Φ.commShiftIso n).app E).symm⟩
      ext₂' := fun T hT h₁ h₃ => ObjectProperty.le_isoClosure _ _
        (RingedSite.isPerfect_obj₂_of_distinguished_general (smallEtaleRingedSite B S hS Y.1 Y.2)
          (Φ.mapTriangle.obj T) (Φ.map_distinguished T hT) h₁ h₃) },
    CategoryTheory.Pretriangulated.isStableUnderRetracts_inverseImage _ _⟩

end AlgebraicGeometry.Space

end

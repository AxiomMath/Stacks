module

public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.AmplitudeFieldPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeEnoughFields
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectLocalOnSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedPerfectAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SingleDegreeFreeGeometricPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SingleDegreeFreeLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SingleDegreeRankOpenSubspaceExistence
public import StacksFrontier.Homology.Perfect.Local

/-!
# A pseudo-coherent complex whose derived fibres are free in one degree

Let `Y` be a quasi-compact algebraic space and `E ∈ D(𝒪_Y)` pseudo-coherent.

1. If at every field-valued point `y : Spec k ⟶ Y` the derived fibre `Ly^*E` has no cohomology
   outside `[a, b]`, then `E` is perfect. This is Stacks 068V read on an affine étale chart: on a
   surjective étale chart `h_{Spec A} ⟶ Y` the pullback of `E` is `ε^*(P~)` for a bounded above
   complex `P` of finite free `A`-modules, the derived fibres of `P` at the primes of `A` are
   derived fibres of `E` at field-valued points, so `P` is a perfect object of `D(A)`, and a
   perfect object of `D(A)` gives a perfect object on `h_{Spec A}` (Stacks 08HG), which is
   enough since perfectness is étale local.
2. If at every field-valued point `Ly^*E ≅ 𝒪^{⊕r}[-n]`, then `E` is a finite locally free module
   of rank `r` placed in degree `n`: `E` is perfect by (1), a perfect complex free in one degree
   at a geometric point is free in that degree on an étale chart through the point
   (`AlgebraicGeometry.Space.pointsMap_mem_singleDegreeFreePoints`, Stacks 0BCD), and that shape
   is étale local (`AlgebraicGeometry.Space.isFiniteLocallyFreeOfIntRankInDegree_iff`).

## Main results

* `isPerfect_of_isPseudoCoherent_of_forall_fieldValuedPoint_isZero_homology`: a pseudo-coherent
  complex whose derived fibres at field-valued points vanish outside `[a, b]` is perfect.
* `isFiniteLocallyFreeOfIntRankInDegree_of_forall_fieldValuedPoint`: a pseudo-coherent complex
  whose derived fibres at field-valued points are free of rank `r` in degree `n` is a finite
  locally free module of rank `r` in degree `n`.

## References

* [Stacks Project, Tag 068V](https://stacks.math.columbia.edu/tag/068V)
* [Stacks Project, Tag 08HG](https://stacks.math.columbia.edu/tag/08HG)
* [Stacks Project, Tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

open scoped Stacks.StandardDerivedModel

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {Y : AlgebraicSpaces B S hS}

/-- **The derived fibres of the chart model are derived fibres of `E`.** Let `φ : h_{Spec A} ⟶ Y`
be étale with `φ^*E ≅ ε^*(P~)` for a bounded above complex `P` of finite free `A`-modules. If
`H^i(Ly^*E) = 0` at every field-valued point `y` of `Y`, then `H^i(κ(𝔭) ⊗_A P) = 0` at every
prime `𝔭` of `A`. -/
theorem isZero_homology_extendScalars_residueField_of_forall_fieldValuedPoint {A : Type u}
    [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A))) (g : B.obj hA ⟶ B.obj hS)
    (φ : (schemeSpace (specFppfOver B S hS hA g) :
      AlgebraicSpaces B S hS) ⟶ Y) (hφ : IsEtale B S hS φ.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree P)
    (eP : letI := etaleModulePullback_additive.{u, u} B S hS φ hφ
      letI := preservesFiniteLimits_etaleModulePullback B S hS φ hφ
      letI := preservesFiniteColimits_etaleModulePullback B S hS φ hφ
      (etaleModulePullback.{u, u} B S hS φ hφ).mapDerivedCategory.obj E ≅
        (representedDerivedAssociatedModule B S hS (specFppfOver B S hS hA g)).obj
          ((tilde.functor (CommRingCat.of A) ⋙ Scheme.Modules.restrictFunctor
            (Iso.refl ((BigFppfOver.toScheme B S hS).obj
              (specFppfOver B S hS hA g))).hom).mapDerivedCategory.obj
            (DerivedCategory.Q.obj P)))
    (i : ℤ)
    (h : ∀ p : FieldValuedPoint B S hS Y.1,
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((smallEtaleDerivedModulePullback B S hS p.toSpace).obj E)))
    (p : PrimeSpectrum A) :
    IsZero (((CochainComplex.extendScalars (algebraMap A p.asIdeal.ResidueField)).obj P).homology
      i) := by
  let := etaleModulePullback_additive.{u, u} B S hS φ hφ
  let := preservesFiniteLimits_etaleModulePullback B S hS φ hφ
  let := preservesFiniteColimits_etaleModulePullback B S hS φ hφ
  let κ := p.asIdeal.ResidueField
  have hκ : B.Contains (Spec (CommRingCat.of κ)) :=
    BigFppfSite.contains_spec_residueField_atPrime B hA p.asIdeal
  let gκ : B.obj hκ ⟶ B.obj hS :=
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap A κ))) :
      B.obj hκ ⟶ B.obj hA) ≫ g
  let j := specFppfOverMap B S hS hA g hκ gκ rfl
  have := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS
    (schemeSpaceMap j)
  obtain ⟨e₆⟩ := nonempty_smallEtaleDerivedModulePullback_chartModel_iso B S hS hA g hκ gκ rfl
    P hP
  obtain ⟨e₅⟩ := nonempty_etaleModulePullback_mapDerivedCategory_iso φ hφ E
  let r : FieldValuedPoint B S hS (yoneda.obj (specFppfOver B S hS hA g)) :=
    ⟨κ, hκ, gκ.hom, j⟩
  have hr : FieldValuedPoint.toSpace (Y := schemeSpace (specFppfOver B S hS hA g)) r =
      schemeSpaceMap j :=
    ObjectProperty.hom_ext _ (yonedaEquiv.symm_apply_eq.2 (yonedaEquiv_yoneda_map j).symm)
  have ht : (r.map B S hS _ φ.hom).toSpace = schemeSpaceMap j ≫ φ := by
    rw [FieldValuedPoint.toSpace_map (Y := Y) φ r, hr]
  have := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS φ
  have := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS
    (schemeSpaceMap j ≫ φ)
  have hz := h (r.map B S hS _ φ.hom)
  rw [ht] at hz
  let e : (smallEtaleDerivedModulePullback B S hS (schemeSpaceMap j ≫ φ)).obj E ≅
      _ := ((smallEtaleDerivedPullbackCompIsoOfTwoIso B S hS (schemeSpaceMap j)
        φ).app E).symm ≪≫
      (smallEtaleDerivedModulePullback B S hS (schemeSpaceMap j)).mapIso
        (e₅.symm ≪≫ eP) ≪≫ e₆
  exact isZero_homology_of_isZero_homology_chartModel hκ gκ _ i
    (hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e.symm))

/-- **Stacks 068V on a quasi-compact algebraic space.** A pseudo-coherent `E ∈ D(𝒪_Y)` whose
derived fibres `Ly^*E` at all field-valued points `y` have no cohomology outside `[a, b]` is
perfect. -/
theorem isPerfect_of_isPseudoCoherent_of_forall_fieldValuedPoint_isZero_homology
    (Y : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS Y.1)
    (E : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (hE : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent E) (a b : ℤ)
    (h : ∀ (p : FieldValuedPoint B S hS Y.1) (i : ℤ), i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((smallEtaleDerivedModulePullback B S hS p.toSpace).obj E))) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect E := by
  obtain ⟨A, _, hA, g, φ, hφ, hφs⟩ := exists_specFppfOver_surjective_etale_chart B S hS Y hqc
  let := etaleModulePullback_additive.{u, u} B S hS φ hφ
  let := preservesFiniteLimits_etaleModulePullback B S hS φ hφ
  let := preservesFiniteColimits_etaleModulePullback B S hS φ hφ
  obtain ⟨P, hP, ⟨eP⟩⟩ := exists_isBoundedAboveFiniteFree_etaleModulePullback_iso B S hS hA g φ hφ
    E hE
  have hK : StacksDraft.PseudoCoherence.IsPseudoCoherent (DerivedCategory.Q.obj P) :=
    ⟨P, hP, ⟨Iso.refl _⟩⟩
  have hvan : ∀ q : PrimeSpectrum A, ∀ i : ℤ, i < a ∨ b < i →
      StacksDraft.Perfect.FibreCohomologyVanishes.{u, u} q.asIdeal (DerivedCategory.Q.obj P) i :=
    fun q i hi =>
    ⟨P, hP, ⟨Iso.refl _⟩,
      isZero_homology_extendScalars_residueField_of_forall_fieldValuedPoint hA g φ hφ E P hP eP i
        (fun p => h p i hi) q⟩
  have hperf : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj P) :=
    ((StacksDraft.Perfect.isPerfect_and_torAmplitude_iff_fibreCohomologyVanishes.{u, u} _ hK a
      b).1.2 hvan).1
  obtain ⟨C, c, d, hc, hd, hfin, hproj, ⟨eC⟩⟩ := hperf
  have hCb : {i : ℤ | ¬ IsZero (C.X i)}.Finite :=
    (Set.finite_Icc c d).subset fun i hi =>
      ⟨not_lt.1 fun hlt => hi (C.isZero_of_isStrictlyGE c i (by lia)),
        not_lt.1 fun hlt => hi (C.isZero_of_isStrictlyLE d i (by lia))⟩
  obtain ⟨K, hK', ⟨e'⟩⟩ :=
    isPerfect_representedDerivedAssociatedModule_Q_tilde B S hS hA g.hom C hCb hfin hproj
  have := AlgebraicGeometry.tilde.preservesFiniteLimits (CommRingCat.of A)
  have : PreservesFiniteColimits (tilde.functor (CommRingCat.of A)) :=
    Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor (CommRingCat.of A)
  let T := tilde.functor (CommRingCat.of A)
  let eQ : DerivedCategory.Q.obj ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj C) ≅
      DerivedCategory.Q.obj ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
    (T.mapDerivedCategoryFactors.app C).symm ≪≫ T.mapDerivedCategory.mapIso eC.symm ≪≫
      T.mapDerivedCategoryFactors.app P
  let e : (representedDerivedAssociatedModule B S hS (specFppfOver B S hS hA g)).obj
      (DerivedCategory.Q.obj ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj C)) ≅
      (etaleModulePullback.{u, u} B S hS φ hφ).mapDerivedCategory.obj E :=
    (representedDerivedAssociatedModule B S hS (specFppfOver B S hS hA g)).mapIso
      (eQ ≪≫ (chartModelTildeIso B S hS hA g P).symm) ≪≫ eP.symm
  refine isPerfect_of_isPerfect_etaleModulePullback B S hS (ι := PUnit.{1}) (fun _ => φ)
    (fun _ => hφ) (fun x => ⟨⟨⟩, hφs x⟩) E fun _ => ⟨K, hK', ⟨e' ≪≫ e⟩⟩

/-- **A pseudo-coherent complex which is free of rank `r` in degree `n` at every field-valued
point is a finite locally free module of rank `r` placed in degree `n`**, on a quasi-compact
algebraic space. -/
theorem isFiniteLocallyFreeOfIntRankInDegree_of_forall_fieldValuedPoint
    (Y : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS Y.1)
    (E : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (hE : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent E) (n r : ℤ)
    (h : ∀ p : FieldValuedPoint B S hS Y.1,
      IsFreeOfRankInDegree ((smallEtaleDerivedModulePullback B S hS p.toSpace).obj E) n r) :
    IsFiniteLocallyFreeOfIntRankInDegree B S hS Y E n r := by
  have hperf : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect E := by
    refine isPerfect_of_isPseudoCoherent_of_forall_fieldValuedPoint_isZero_homology Y hqc E hE n n
      fun p i hi => ?_
    obtain ⟨m, -, ⟨e⟩⟩ := h p
    refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ i).mapIso e)
    rcases hi with hlt | hlt
    · exact DerivedCategory.isZero_of_isGE _ n i hlt
    · exact DerivedCategory.isZero_of_isLE _ n i hlt
  refine (isFiniteLocallyFreeOfIntRankInDegree_iff B S hS Y E n r).2 fun y => ?_
  obtain ⟨t, rfl⟩ := (geometricPoints_large_enough B S hS _ _ Y.2 Y.2).1 y
  obtain ⟨V, hV, hfree⟩ :=
    pointsMap_mem_singleDegreeFreePoints B S hS E hperf n r t t.val.toSpace (h t.val)
  have htaut := pointsMap_yonedaEquiv_symm_comp_tautological t (𝟙 _)
  rw [Category.comp_id, pointsMap_id] at htaut
  have hpt : pointsMap B S hS _ t.val.toSpace.hom (GeometricPoint.tautological B S hS t).image =
      t.image := htaut
  exact ⟨V, hpt ▸ hV, hfree⟩

end AlgebraicGeometry.Space

end

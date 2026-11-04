module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperSupportDerivedPushforwardCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectTensorFlatPullbackBound
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.StrictlyPerfectTensorBound
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.PseudoCoherentIffCoherentHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedTensorClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissage

/-!
# Coherent cohomology of `P ⊗^L H` with `P` strictly perfect

On an algebraic space `Z`, a bounded complex of coherent modules has coherent cohomology, and so
has `P ⊗^L H` for `P` a bounded complex of retracts of finite free modules and `H` with coherent
cohomology, when the structure sheaf of `Z` is coherent. Along the stupid filtration of `P` this
reduces to a single retract of `𝒪_Z^{⊕ n}`, where it is the unit law.

## Main results

* `AlgebraicGeometry.Space.derivedCategoryB_isCoherent_Q_of_isCoherent`
* `AlgebraicGeometry.Space.derivedCategoryB_isCoherent_tensor_of_strictlyPerfect`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (Z : AlgebraicSpaces B S hS)

/-- The objects of `D(𝒪_Z)` with coherent cohomology. -/
abbrev coherentDerivedObjects : ObjectProperty
    (DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))) :=
  DerivedCategoryB.derivedCategoryB (isCoherent.{u, u} B S hS Z.1 Z.2)

/-- Coherence, read on the modules of `ringedToposStructureRingSheaf`, is a weak Serre class. -/
theorem isWeakSerre_isCoherent_smallEtale :
    WeakSerre.IsWeakSerre (A := SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))
      (isCoherent.{u, u} B S hS Z.1 Z.2) :=
  @WeakSerre.isWeakSerre_of_isWeakSerreClass _ _ _ _
    (isCoherent_isWeakSerreClass_smallEtale B S hS Z.1 Z.2)

/-- The objects of `D(𝒪_Z)` with coherent cohomology form a triangulated subcategory. -/
instance coherentDerived_isTriangulated : (coherentDerivedObjects Z).IsTriangulated :=
  DerivedCategoryB.derivedCategoryB_isTriangulated _ (isWeakSerre_isCoherent_smallEtale Z)

/-- Having coherent cohomology is invariant under isomorphisms in `D(𝒪_Z)`. -/
instance coherentDerived_isClosedUnderIsomorphisms :
    (coherentDerivedObjects Z).IsClosedUnderIsomorphisms :=
  DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms _
    (isWeakSerre_isCoherent_smallEtale Z)

/-- **A bounded complex of coherent modules has coherent cohomology.** -/
theorem derivedCategoryB_isCoherent_Q_of_isCoherent
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)) ℤ)
    (hGb : {i : ℤ | ¬ IsZero (G.X i)}.Finite) (hG : ∀ n, IsCoherent B S hS Z.1 Z.2 (G.X n)) :
    coherentDerivedObjects Z (DerivedCategory.Q.obj G) :=
  StacksDraft.ExtremalDegrees.prop_map_Q_of_terms (𝟭 _) (coherentDerivedObjects Z) G hGb fun i _ =>
    (DerivedCategoryB.derivedCategoryBPlus_singleFunctor_obj _
      (isWeakSerre_isCoherent_smallEtale Z) (G.X i) (hG i)).2

/-- **`P ⊗^L H` has coherent cohomology** for `P` a bounded complex of retracts of finite free
modules and `H` with coherent cohomology. -/
theorem derivedCategoryB_isCoherent_tensor_of_strictlyPerfect
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)) ℤ)
    (hP : ∀ j, IsRetractOfFiniteFree
      (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Z)) (P.X j))
    (hPb : {i : ℤ | ¬ IsZero (P.X i)}.Finite)
    (H : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)))
    (hH : coherentDerivedObjects Z H) :
    coherentDerivedObjects Z
      (((smallEtaleDerivedTensor B S hS Z).obj (DerivedCategory.Q.obj P)).obj H) := by
  let T := smallEtaleDerivedTensorProduct B S hS Z
  let : ((smallEtaleDerivedTensor B S hS Z).flip.obj H).CommShift ℤ := T.commShift_left H
  have : ((smallEtaleDerivedTensor B S hS Z).flip.obj H).IsTriangulated := T.exact_left H
  refine StacksDraft.ExtremalDegrees.prop_map_Q_of_terms
    ((smallEtaleDerivedTensor B S hS Z).flip.obj H) (coherentDerivedObjects Z) P hPb fun i _ => ?_
  obtain ⟨n, ι, π, hιπ⟩ := hP i
  let O := SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Z)
  let sΦ := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)) 0 ⋙
    (smallEtaleDerivedTensor B S hS Z).flip.obj H
  have hunit : coherentDerivedObjects Z (sΦ.obj O) := by
    let e₀ := (smallEtaleDerivedTensor B S hS Z).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).app O) ≪≫
      T.leftSingleUnitNatIso 0 ≪≫ shiftFunctorZero' _ (-0 : ℤ) (by simp)
    exact (coherentDerivedObjects Z).prop_of_iso (e₀.app H).symm hH
  have hfree : coherentDerivedObjects Z (sΦ.obj (⨁ fun _ : Fin n => O)) :=
    (coherentDerivedObjects Z).prop_of_iso (sΦ.mapBiproduct fun _ : Fin n => O).symm
      ((coherentDerivedObjects Z).prop_of_isLimit_fan (biproduct.isLimit _) fun _ => hunit)
  have hst :=
    DerivedCategoryB.derivedCategoryB_isStableUnderRetracts _ (isWeakSerre_isCoherent_smallEtale Z)
  exact (coherentDerivedObjects Z).prop_of_retract
    ⟨sΦ.map ι, sΦ.map π, by rw [← sΦ.map_comp, hιπ, CategoryTheory.Functor.map_id]; rfl⟩ hfree

variable {Z} in
/-- **`E ⊗^L 𝒢^•` has coherent cohomology** on a locally Noetherian algebraic space, for `E`
perfect and `𝒢^•` a bounded complex of coherent modules. On an affine étale chart `p : W ⟶ X`,
`Lp^*E` has a strictly perfect model and `p^*𝒢^•` is a bounded complex of coherent modules, so the
cohomology of `Lp^*(E ⊗^L 𝒢^•)` is coherent and its sections over `W` are finite. -/
theorem derivedCategoryB_isCoherent_tensor_of_isPerfect
    (hN : HasEtaleLocalProperty B S hS Z.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Z.1 Z.2) E)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)) ℤ)
    (hGb : {i : ℤ | ¬ IsZero (G.X i)}.Finite) (hG : ∀ n, IsCoherent B S hS Z.1 Z.2 (G.X n)) :
    coherentDerivedObjects Z
      (((smallEtaleDerivedTensor B S hS Z).obj E).obj (DerivedCategory.Q.obj G)) := by
  set K := ((smallEtaleDerivedTensor B S hS Z).obj E).obj (DerivedCategory.Q.obj G)
  have hGc := derivedCategoryB_isCoherent_Q_of_isCoherent Z G hGb hG
  have hGq : QcohDerived B S hS Z (DerivedCategory.Q.obj G) := fun n =>
    (hGc n).toIsQuasicoherentOnSite
  have hKq : QcohDerived B S hS Z K :=
    qcohDerived_smallEtaleDerivedTensor Z E _ (qcohDerived_of_isPerfect_derivedCategoryB Z E hE) hGq
  intro k
  refine isCoherent_of_isQuasicoherentOnSite_of_forall_affine_moduleFinite B S hS Z.1 Z.2 hN _
    (hKq k) fun A hA => ?_
  let U₀ := (SmallEtale.toOver B S hS Z.1).obj A
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀) := hA
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U₀) :=
    isLocallyNoetherian_chart B S hS hN A
  have hloc : Fact (HasEtaleLocalProperty B S hS (yoneda.obj U₀)
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
    ⟨hasEtaleLocalProperty_of_representable B S hS _ _ U₀ (Iso.refl _) inferInstance⟩
  have : Fact (HasEtaleLocalProperty B S hS (chartSpace B S hS Z A).obj
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) := hloc
  let p := chartToSpace B S hS Z A
  have hp := isEtale_chartToSpace B S hS Z A
  -- the derived pullback of `K` has coherent cohomology
  have hEW := isPerfect_smallEtaleDerivedModulePullback p E hE
  obtain ⟨P, hP, ⟨c, d, hc, hd⟩, ⟨eP⟩⟩ := hasStrictlyPerfectModel_of_isCompactObject_yoneda U₀
    ⟨_, qcohDerived_of_isPerfect_derivedCategoryB (schemeSpace U₀) _ hEW⟩
    (isCompactObject_of_isPerfect_yoneda U₀ _ hEW)
  have hPb : {i : ℤ | ¬ IsZero (P.X i)}.Finite := by
    refine (Set.finite_Icc c d).subset fun i hi => ⟨?_, ?_⟩
    · by_contra h
      exact hi (P.isZero_of_isStrictlyGE c i (by omega))
    · by_contra h
      exact hi (P.isZero_of_isStrictlyLE d i (by omega))
  let G' := ((modulePullback B S hS p).mapHomologicalComplex (ComplexShape.up ℤ)).obj G
  have hG'b : {i : ℤ | ¬ IsZero (G'.X i)}.Finite :=
    hGb.subset fun i hi h => hi ((modulePullback B S hS p).map_isZero h)
  have hG'c := derivedCategoryB_isCoherent_Q_of_isCoherent (schemeSpace U₀) G' hG'b
    fun n => isCoherent_modulePullback B S hS p (G.X n) (hG n)
  have hW := derivedCategoryB_isCoherent_tensor_of_strictlyPerfect (schemeSpace U₀) P hP hPb _ hG'c
  let e : (smallEtaleDerivedModulePullback B S hS p).obj K ≅
      ((smallEtaleDerivedTensor B S hS (schemeSpace U₀)).obj (DerivedCategory.Q.obj P)).obj
        (DerivedCategory.Q.obj G') :=
    (smallEtaleDerivedPullbackTensorIso p).app (E, DerivedCategory.Q.obj G) ≪≫
      ((smallEtaleDerivedTensor B S hS (schemeSpace U₀)).mapIso eP).app _ ≪≫
      ((smallEtaleDerivedTensor B S hS (schemeSpace U₀)).obj _).mapIso
        (smallEtaleDerivedModulePullbackObjQIsoOfIsEtale p hp G)
  let eH : (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS (yoneda.obj U₀)
      (isAlgebraicSpace_yoneda B S hS U₀)) k).obj
        ((smallEtaleDerivedModulePullback B S hS p).obj K) ≅
      (etaleModulePullback.{u, u} B S hS p hp).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Z.1 Z.2) k).obj K) :=
    smallEtaleDerivedModulePullbackHomologyIsoOfIsEtale p hp K k ≪≫
      (modulePullbackIsoEtaleModulePullback B S hS p hp).app _
  have hcoh : IsCoherent B S hS (yoneda.obj U₀) (isAlgebraicSpace_yoneda B S hS U₀)
      ((etaleModulePullback.{u, u} B S hS p hp).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Z.1 Z.2) k).obj K)) :=
    isCoherent_of_iso B S hS _ ((DerivedCategory.homologyFunctor _ k).mapIso e.symm ≪≫ eH) (hW k)
  exact moduleFinite_sections_of_isCoherent B S hS (yoneda.obj U₀)
    (isAlgebraicSpace_yoneda B S hS U₀) _ hcoh (V := idEtaleChart B S hS U₀) hA

end AlgebraicGeometry.Space

end

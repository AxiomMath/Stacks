module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectTensorSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.StrictlyPerfectTensorCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetUnion
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportClosedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse

/-!
# Proper support of the cohomology of a tensor product

Declarations supplementing `StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectTensorSupport`
(`hasProperSupport_homology_tensor`, `supportOfSheaf_homology_tensor_subset`), kept in their
own module.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- **The support of `Hⁱ(E ⊗^L 𝒢^•)` lies in the union of the supports of the `𝒢ⁿ`.** -/
theorem supportOfSheaf_homology_tensor_subset
    (hN : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hGb : {i : ℤ | ¬ IsZero (G.X i)}.Finite) (hG : ∀ n, IsCoherent B S hS X.1 X.2 (G.X n))
    (i : ℤ) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj
          (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G)))) ⊆
      ⋃ n ∈ hGb.toFinset, supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj (G.X n)) := by
  set M := ((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G)
  set T := ⋃ n ∈ hGb.toFinset, supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj (G.X n))
  have hTcl : IsClosed T := by
    refine hGb.toFinset.finite_toSet.isClosed_biUnion fun n _ => ?_
    have := (hG n).toIsCoherentOnSite
    exact @isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X.1 X.2 (G.X n)
      (isFiniteTypeOnSite_of_isCoherentOnSite B S hS X (G.X n))
  obtain ⟨V, hV, hrange⟩ := exists_isOpenSubspace_range_pointsMap_eq B S hS X.2 Tᶜ hTcl.isOpen_compl
  let W : AlgebraicSpaces B S hS := ⟨V.toFunctor, hV.1⟩
  let j : W ⟶ X := ObjectProperty.homMk V.ι
  have hj : IsEtale B S hS j.hom := isEtale_ι_of_isOpenSubspace hV
  have hGW : ∀ n, IsZero ((modulePullback B S hS j).obj (G.X n)) := fun n => by
    have := (hG n).toIsCoherentOnSite
    refine (supportOfSheaf_eq_empty_iff_isZero B S hS W _).1 ?_
    rw [supportOfSheaf_modulePullback_eq B S hS j (G.X n) (hG n).toIsQuasicoherentOnSite
      (isFiniteTypeOnSite_of_isCoherentOnSite B S hS X (G.X n))]
    refine Set.eq_empty_of_forall_notMem fun w hw => ?_
    have hwT : pointsMap B S hS W.1 j.hom w ∈ Tᶜ := by
      rw [← hrange]
      exact ⟨w, rfl⟩
    refine hwT ?_
    by_cases hn : n ∈ hGb.toFinset
    · exact Set.mem_biUnion hn hw
    · have hz : IsZero (G.X n) := of_not_not fun h => hn (hGb.mem_toFinset.2 h)
      rw [(supportOfSheaf_eq_empty_iff_isZero B S hS X _).2 hz] at hw
      exact absurd hw (Set.notMem_empty _)
  -- `Lj^*M = 0`
  have hQ : IsZero ((smallEtaleDerivedModulePullback B S hS j).obj (DerivedCategory.Q.obj G)) := by
    refine IsZero.of_iso ?_ (smallEtaleDerivedModulePullbackObjQIsoOfIsEtale j hj G)
    refine DerivedCategory.Q.map_isZero ?_
    refine (IsZero.iff_id_eq_zero _).2 (HomologicalComplex.hom_ext _ _ fun n => ?_)
    exact (hGW n).eq_of_src _ _
  have hM : IsZero ((smallEtaleDerivedModulePullback B S hS j).obj M) := by
    have h0 : IsZero (((smallEtaleDerivedTensorProduct B S hS W).tensor.obj
        ((smallEtaleDerivedModulePullback B S hS j).obj E)).obj
          ((smallEtaleDerivedModulePullback B S hS j).obj (DerivedCategory.Q.obj G))) := by
      let := (smallEtaleDerivedTensorProduct B S hS W).commShift_right
        ((smallEtaleDerivedModulePullback B S hS j).obj E)
      have := (smallEtaleDerivedTensorProduct B S hS W).exact_right
        ((smallEtaleDerivedModulePullback B S hS j).obj E)
      exact Functor.map_isZero _ hQ
    exact h0.of_iso ((smallEtaleDerivedPullbackTensorIso j).app (E, DerivedCategory.Q.obj G))
  have hcoh := derivedCategoryB_isCoherent_tensor_of_isPerfect hN E hE G hGb hG i
  have := hcoh.toIsCoherentOnSite
  have hHW : IsZero ((modulePullback B S hS j).obj
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj M)) :=
    ((DerivedCategory.homologyFunctor _ i).map_isZero hM).of_iso
      (smallEtaleDerivedModulePullbackHomologyIsoOfIsEtale j hj M i).symm
  have hsupp := (supportOfSheaf_eq_empty_iff_isZero B S hS W _).2 hHW
  rw [supportOfSheaf_modulePullback_eq B S hS j
    ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj M)
    hcoh.toIsQuasicoherentOnSite
    (@isFiniteTypeOnSite_of_isCoherentOnSite B S hS X _ hcoh.toIsCoherentOnSite)] at hsupp
  intro x hx
  by_contra hxT
  obtain ⟨w, rfl⟩ : x ∈ Set.range (pointsMap B S hS V.toFunctor V.ι) := by rwa [hrange]
  exact Set.eq_empty_iff_forall_notMem.1 hsupp w hx

/-- **The cohomology sheaves of `E ⊗^L 𝒢^•` have support proper over `Y`** when the terms of
`𝒢^•` do, on a locally Noetherian algebraic space, for `E` perfect and `𝒢^•` a bounded complex
of coherent modules. -/
theorem hasProperSupport_homology_tensor
    (hN : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))
    (f : X ⟶ Y) (hft : IsLocallyOfFiniteType B S hS f.hom)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hGb : {i : ℤ | ¬ IsZero (G.X i)}.Finite) (hG : ∀ n, IsCoherent B S hS X.1 X.2 (G.X n))
    (hsupp : ∀ n, HasProperSupport B S hS X.2 Y.2 f.hom hft
      ((SheafOfModules.toSheaf _).obj (G.X n))) (i : ℤ) :
    HasProperSupport B S hS X.2 Y.2 f.hom hft ((SheafOfModules.toSheaf _).obj
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj
        (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G)))) := by
  have hcoh := derivedCategoryB_isCoherent_tensor_of_isPerfect hN E hE G hGb hG i
  have hcl := @isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X.1 X.2 _
    (@isFiniteTypeOnSite_of_isCoherentOnSite B S hS X _ hcoh.toIsCoherentOnSite)
  let ι := {n : ℤ // n ∈ hGb.toFinset}
  let T : ι → Set (points B S hS X.1) := fun n =>
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj (G.X n.1))
  have hT : ∀ n, IsClosed (T n) := fun n => (hsupp n.1).1
  refine ⟨hcl, isProperOver_of_subset B S hS X.2 Y.2 f.hom hft _ _ hcl
    (isClosed_iUnion_of_finite hT) ?_
    (isProperOver_iUnion B S hS X.2 Y.2 f.hom hft T hT fun n => (hsupp n.1).2)⟩
  intro x hx
  obtain ⟨n, hn, hxn⟩ :=
    Set.mem_iUnion₂.1 (supportOfSheaf_homology_tensor_subset hN E hE G hGb hG i hx)
  exact Set.mem_iUnion.2 ⟨⟨n, hn⟩, hxn⟩

end AlgebraicGeometry.Space

end

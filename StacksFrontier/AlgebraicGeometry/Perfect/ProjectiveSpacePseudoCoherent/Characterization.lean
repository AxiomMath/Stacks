module

public import
  StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveSpaceDirectImage.RelativeAffineCriterion
public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveSpaceDirectImage.RelativeProjectiveBundlePseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveSpacePseudoCoherent.Approximation
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatDerivedSectionsPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectFibreHomVanishing
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.ExampleGenerator.CohomologicalBound
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessLeray
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeConverse
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualAtTheSpaceHypothesis
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualTensorHomFunctorial
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.DerivedTensorProduct

/-!
# Characterizing pseudo-coherent objects on `ℙⁿ_A` by their cohomology

Let `A` be a ring, `X = ℙⁿ_A` and `K ∈ D_QCoh(𝒪_X)`. This file proves the implications of
[Stacks, Tag 0CSG]: if `K` is pseudo-coherent then so is `RΓ(X, E ⊗^𝐋 K)` for all pseudo-coherent
`E`; this implies it for all perfect `E`, which is equivalent to pseudo-coherence of
`RΓ(X, R𝓗om(E, K))` for all perfect `E` and implies pseudo-coherence of `RΓ(X, K ⊗^𝐋 𝒪(d))` for
`0 ≤ d ≤ n`; and the latter implies that `K` is pseudo-coherent.

## Main results

All in the namespace `AlgebraicGeometry.ProjectiveSpacePseudoCoherent`:

* `isPseudoCoherent_derivedGlobalSectionsOver_of_isPseudoCoherent`: `RΓ(ℙⁿ_A, -)` carries
  pseudo-coherent objects to pseudo-coherent objects of `D(A)`.
* `isPseudoCoherent_tensor_of_isPseudoCoherent`: if `K` is pseudo-coherent, then
  `RΓ(X, E ⊗^𝐋 K)` is pseudo-coherent for every pseudo-coherent `E`.
* `isPseudoCoherent_derivedSheafHom_of_isPerfect` and
  `isPseudoCoherent_tensor_of_isPseudoCoherent_derivedSheafHom`: for perfect `E`,
  pseudo-coherence of all `RΓ(X, E ⊗^𝐋 K)` and of all `RΓ(X, R𝓗om(E, K))` are equivalent.
* `isLE_of_isZero_homology_testFunctor`: if `Hʲ(X, Z(d)) = 0` for `0 ≤ d ≤ n` and `j ≥ m`, then
  `Z ∈ D^{≤ m - 1}`.
* `isPseudoCoherent_of_testPseudoCoherent` and `isPseudoCoherent_of_isPseudoCoherent_twist`: if
  `RΓ(X, K ⊗^𝐋 𝒪(d))` is pseudo-coherent for `0 ≤ d ≤ n`, then `K` is pseudo-coherent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open Stacks.AlgebraicGeometry.ProjTwistFunctor
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

namespace AlgebraicGeometry.ProjectiveSpacePseudoCoherent

variable (A : Type u) [CommRing A] (n : ℕ)

/-- If `Z ∈ D_QCoh(𝒪_X)` has `Hʲ(X, Z(d)) = 0` for `0 ≤ d ≤ n` and `j ≥ m`, then
`Z ∈ D^{≤ m - 1}`. -/
theorem isLE_of_isZero_homology_testFunctor (Z : DerivedCategory (Proj (polyGrading A n)).Modules)
    (hZ : quasicoherentObject A n Z) (m : ℤ)
    (h : ∀ (d : Fin (n + 1)) (j : ℤ), m ≤ j →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj
        ((testFunctor A n d).obj Z))) :
    Z.IsLE (m - 1) :=
  Stacks.AlgebraicGeometry.ExampleGenerator.isLE_of_hom_singleFunctor_twistingSheaf_eq_zero
    (A := A) (n := n) Z hZ m fun d j hj f => by
      have hx := eq_zero_of_isZero_homology_testFunctor A n (d : ℤ) Z j (h d j hj)
        ((testObjectIso A n (d : ℤ)).hom ≫ f)
      rw [← cancel_epi (testObjectIso A n (d : ℤ)).hom, hx, comp_zero]

/-- Let `K ∈ D_QCoh(𝒪_X)` with `RΓ(X, K(d))` pseudo-coherent for `0 ≤ d ≤ n`, in the form of
`testPseudoCoherent`. Then `K` is pseudo-coherent. -/
theorem isPseudoCoherent_of_testPseudoCoherent
    (K : DerivedCategory (Proj (polyGrading A n)).Modules) (hK : quasicoherentObject A n K)
    (hK' : testPseudoCoherent A n K) :
    RingedSpace.IsPseudoCoherent (X := (Proj (polyGrading A n)).toRingedSpace) K := by
  refine (Scheme.isPseudoCoherentObject_iff_forall _ K).2 fun m => ?_
  obtain ⟨Y, Z, α, β, γ, hT, hY, hZ⟩ :=
    exists_distTriang_isZero_homology_testFunctor A n K hK' m
  have hZq : quasicoherentObject A n Z := by
    obtain ⟨Z', hZ', ⟨e⟩⟩ := (quasicoherentObject A n).ext_of_isTriangulatedClosed₃' _ hT hY.1 hK
    exact (quasicoherentObject A n).prop_of_iso e.symm hZ'
  have hZm : RingedSpace.IsPseudoCoherentFrom (X := (Proj (polyGrading A n)).toRingedSpace) Z m :=
    @RingedSpace.isPseudoCoherentFrom_of_isLE (Proj (polyGrading A n)).toRingedSpace _ Z m
      (isLE_of_isZero_homology_testFunctor A n Z hZq m hZ)
  exact RingedSpace.isPseudoCoherentFrom_obj₂_of_distinguished
    (X := (Proj (polyGrading A n)).toRingedSpace) m _ hT
    (((Scheme.isPseudoCoherentObject_iff_forall _ Y).1 hY.2.1) m) hZm

/-- Let `K ∈ D_QCoh(𝒪_X)` with `RΓ(X, K ⊗^𝐋 𝒪(d))` pseudo-coherent for `0 ≤ d ≤ n`. Then `K` is
pseudo-coherent. -/
theorem isPseudoCoherent_of_isPseudoCoherent_twist
    (K : DerivedCategory (Proj (polyGrading A n)).Modules) (hK : quasicoherentObject A n K)
    (h5 : ∀ d : Fin (n + 1), StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((derivedGlobalSectionsOver (projToSpecCoeff A n)).obj
        (((derivedTensorProductFunctor (Proj (polyGrading A n)).sheaf).obj K).obj
          ((DerivedCategory.singleFunctor (Proj (polyGrading A n)).Modules 0).obj
            (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) d))))) :
    RingedSpace.IsPseudoCoherent (X := (Proj (polyGrading A n)).toRingedSpace) K :=
  isPseudoCoherent_of_testPseudoCoherent A n K hK fun d =>
    (h5 d).ofIso ((derivedGlobalSectionsOver (projToSpecCoeff A n)).mapIso
      (derivedTensorTwistIso A n d K))

/-- If `RΓ(X, E ⊗^𝐋 K)` is pseudo-coherent for every pseudo-coherent `E`, then it is
pseudo-coherent for every perfect `E`. -/
theorem isPseudoCoherent_tensor_of_isPerfect
    (K : DerivedCategory (Proj (polyGrading A n)).Modules)
    (h2 : ∀ E : DerivedCategory (Proj (polyGrading A n)).Modules,
      RingedSpace.IsPseudoCoherent (X := (Proj (polyGrading A n)).toRingedSpace) E →
        StacksDraft.PseudoCoherence.IsPseudoCoherent
          ((derivedGlobalSectionsOver (projToSpecCoeff A n)).obj
            (((derivedTensorProductFunctor (Proj (polyGrading A n)).sheaf).obj E).obj K)))
    (E : DerivedCategory (Proj (polyGrading A n)).Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Proj (polyGrading A n)).toRingedSpace)
      E) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((derivedGlobalSectionsOver (projToSpecCoeff A n)).obj
        (((derivedTensorProductFunctor (Proj (polyGrading A n)).sheaf).obj E).obj K)) :=
  h2 E ((Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent'
    (X := (Proj (polyGrading A n)).toRingedSpace) _).1
    (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect
      (X := (Proj (polyGrading A n)).toRingedSpace) _ hE))

/-- The twisting sheaf `𝒪(d)` in degree zero is perfect. -/
theorem isPerfect_singleFunctor_twistingSheaf (d : ℤ) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Proj (polyGrading A n)).toRingedSpace)
      ((DerivedCategory.singleFunctor (Proj (polyGrading A n)).Modules 0).obj
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) d)) :=
  have := Stacks.AlgebraicGeometry.ProjTwistRank.isFiniteLocallyFreeOfRank_twistingSheaf A n d
  isPerfect_singleFunctor_of_isFiniteLocallyFree (Proj (polyGrading A n))
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) d)
    (SheafOfModules.IsFiniteLocallyFree.toFiniteLocallyFree.{u, u, u} _
      (SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) d) 1))

/-- Pseudo-coherence of `RΓ(X, E ⊗^𝐋 K)` implies that of `RΓ(X, K ⊗^𝐋 E)`. -/
private theorem isPseudoCoherent_tensor_comm
    (E K : DerivedCategory (Proj (polyGrading A n)).Modules)
    (h : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((derivedGlobalSectionsOver (projToSpecCoeff A n)).obj
        (((derivedTensorProductFunctor (Proj (polyGrading A n)).sheaf).obj E).obj K))) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((derivedGlobalSectionsOver (projToSpecCoeff A n)).obj
        (((derivedTensorProductFunctor (Proj (polyGrading A n)).sheaf).obj K).obj E)) :=
  h.ofIso ((derivedGlobalSectionsOver (projToSpecCoeff A n)).mapIso
    (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingIso
      (Stacks.RingedSpace.toRingedSite (Proj (polyGrading A n)).toRingedSpace)
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
        (Proj (polyGrading A n)).sheaf) _ _))

/-- If `RΓ(X, E ⊗^𝐋 K)` is pseudo-coherent for every perfect `E`, then `RΓ(X, K ⊗^𝐋 𝒪(d))` is
pseudo-coherent for every `d`. -/
theorem isPseudoCoherent_tensor_twist_of_isPerfect
    (K : DerivedCategory (Proj (polyGrading A n)).Modules)
    (h3 : ∀ E : DerivedCategory (Proj (polyGrading A n)).Modules,
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Proj (polyGrading A n)).toRingedSpace)
        E →
        StacksDraft.PseudoCoherence.IsPseudoCoherent
          ((derivedGlobalSectionsOver (projToSpecCoeff A n)).obj
            (((derivedTensorProductFunctor (Proj (polyGrading A n)).sheaf).obj E).obj K)))
    (d : ℤ) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((derivedGlobalSectionsOver (projToSpecCoeff A n)).obj
        (((derivedTensorProductFunctor (Proj (polyGrading A n)).sheaf).obj K).obj
          ((DerivedCategory.singleFunctor (Proj (polyGrading A n)).Modules 0).obj
            (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) d)))) :=
  isPseudoCoherent_tensor_comm A n _ _ (h3 _ (isPerfect_singleFunctor_twistingSheaf A n d))

/-- `RΓ(ℙⁿ_A, -)` carries pseudo-coherent objects to pseudo-coherent objects of `D(A)`. -/
theorem isPseudoCoherent_derivedGlobalSectionsOver_of_isPseudoCoherent
    (F : DerivedCategory (Proj (polyGrading A n)).Modules)
    (hF : RingedSpace.IsPseudoCoherent (X := (Proj (polyGrading A n)).toRingedSpace) F) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((derivedGlobalSectionsOver (projToSpecCoeff A n)).obj F) :=
  (isPseudoCoherent_derivedGlobalSectionsOver_id_of_isPseudoCoherent (.of A) _
    (isPseudoCoherent_derivedPushforward_of_iso (projToSpecCoeff A n)
      (projectiveSpaceOver n (Spec (.of A)) ↘ Spec (.of A))
      (asIso (Stacks.AlgebraicGeometry.ProjPolyChart.projCompare A n)) (Iso.refl _)
      (by rw [Iso.refl_hom, Category.comp_id]
          exact Stacks.AlgebraicGeometry.ProjPolyChart.projCompare_fst A n)
      (isPseudoCoherent_derivedPushforward_projectiveSpaceOver_spec n (.of A)) F hF)).ofIso
    ((derivedGlobalSectionsOverPushforwardIso (projToSpecCoeff A n)).app F).symm

/-- If `K` is pseudo-coherent, then `RΓ(X, E ⊗^𝐋 K)` is pseudo-coherent for every
pseudo-coherent `E`. -/
theorem isPseudoCoherent_tensor_of_isPseudoCoherent
    (K : DerivedCategory (Proj (polyGrading A n)).Modules)
    (hK : RingedSpace.IsPseudoCoherent (X := (Proj (polyGrading A n)).toRingedSpace) K)
    (E : DerivedCategory (Proj (polyGrading A n)).Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := (Proj (polyGrading A n)).toRingedSpace) E) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((derivedGlobalSectionsOver (projToSpecCoeff A n)).obj
        (((derivedTensorProductFunctor (Proj (polyGrading A n)).sheaf).obj E).obj K)) :=
  isPseudoCoherent_derivedGlobalSectionsOver_of_isPseudoCoherent A n _
    (RingedSpace.isPseudoCoherent_derivedTensorProduct (Proj (polyGrading A n)).toRingedSpace
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct _) E K hE hK)

/-- If `RΓ(X, E ⊗^𝐋 K)` is pseudo-coherent for every perfect `E`, then so is
`RΓ(X, R𝓗om(E, K))` for every perfect `E`. -/
theorem isPseudoCoherent_derivedSheafHom_of_isPerfect
    (K : DerivedCategory (Proj (polyGrading A n)).Modules)
    (h3 : ∀ E : DerivedCategory (Proj (polyGrading A n)).Modules,
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Proj (polyGrading A n)).toRingedSpace)
        E →
        StacksDraft.PseudoCoherence.IsPseudoCoherent
          ((derivedGlobalSectionsOver (projToSpecCoeff A n)).obj
            (((derivedTensorProductFunctor (Proj (polyGrading A n)).sheaf).obj E).obj K)))
    (E : DerivedCategory (Proj (polyGrading A n)).Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Proj (polyGrading A n)).toRingedSpace)
      E) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((derivedGlobalSectionsOver (projToSpecCoeff A n)).obj
        (((Stacks.SheafOfModules.derivedSheafHom (Proj (polyGrading A n)).sheaf).obj
          (Opposite.op E)).obj K)) :=
  (isPseudoCoherent_tensor_comm A n _ _
    (h3 _ (Stacks.SheafOfModules.isPerfect_derivedDual_of_isPerfectSpace _ E hE))).ofIso
    ((derivedGlobalSectionsOver (projToSpecCoeff A n)).mapIso
      (((derivedTensorSpellingIso (Proj (polyGrading A n))).app K).app _ ≪≫
        (Stacks.SheafOfModules.derivedTensorDualNatIsoOfIsPerfectSpace _ E hE).app K))

/-- If `RΓ(X, R𝓗om(E, K))` is pseudo-coherent for every perfect `E`, then so is
`RΓ(X, E ⊗^𝐋 K)` for every perfect `E`. -/
theorem isPseudoCoherent_tensor_of_isPseudoCoherent_derivedSheafHom
    (K : DerivedCategory (Proj (polyGrading A n)).Modules)
    (h4 : ∀ E : DerivedCategory (Proj (polyGrading A n)).Modules,
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Proj (polyGrading A n)).toRingedSpace)
        E →
        StacksDraft.PseudoCoherence.IsPseudoCoherent
          ((derivedGlobalSectionsOver (projToSpecCoeff A n)).obj
            (((Stacks.SheafOfModules.derivedSheafHom (Proj (polyGrading A n)).sheaf).obj
              (Opposite.op E)).obj K)))
    (E : DerivedCategory (Proj (polyGrading A n)).Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Proj (polyGrading A n)).toRingedSpace)
      E) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((derivedGlobalSectionsOver (projToSpecCoeff A n)).obj
        (((derivedTensorProductFunctor (Proj (polyGrading A n)).sheaf).obj E).obj K)) :=
  isPseudoCoherent_tensor_comm A n _ _
    ((h4 _ (Stacks.SheafOfModules.isPerfect_derivedDual_of_isPerfectSpace _ E hE)).ofIso
      ((derivedGlobalSectionsOver (projToSpecCoeff A n)).mapIso
        (((Stacks.SheafOfModules.derivedTensorDualNatIsoOfIsPerfectSpace _ _
            (Stacks.SheafOfModules.isPerfect_derivedDual_of_isPerfectSpace _ E hE)).app K).symm ≪≫
          (((derivedTensorSpellingIso (Proj (polyGrading A n))).app K).app _).symm ≪≫
          ((derivedTensorProductFunctor (Proj (polyGrading A n)).sheaf).obj K).mapIso
            (Stacks.SheafOfModules.derivedBidualIsoOfIsPerfectSpace _ E hE).symm)))

end AlgebraicGeometry.ProjectiveSpacePseudoCoherent

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectQuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedPerfectAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedPerfectConverseGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPerfect

/-!
# Perfect objects on `h_{Spec A}` are bounded complexes of finite projective `A`-modules

Let `A` be a ring and `T` the object `Spec A` of the big fppf site. Every perfect object `E` of
`D(𝒪_{h_T})` (perfectness on the small étale site, Stacks 08G5) is isomorphic to the image of a
bounded complex `C` of finite projective `A`-modules under the termwise functor
`M ↦ ε^*(M̃)` (`AlgebraicGeometry.Space.representedTilde`).

This is the affine base case of the descent of perfect objects along a limit of algebraic
spaces (Stacks 09RJ) in the form the derived pullback consumes: on a strictly bounded complex of
flat modules the derived pullback is computed termwise.

The proof assembles results of the library: `E` has quasi-coherent cohomology (Stacks 08JL), so
`E ≅ ε^*N` for `N` in `D_QCoh(𝒪_{Spec A})` (Stacks 071Q); `N` is perfect (the converse of
Stacks 08HG); `N ≅ M̃` for `M` in `D(A)` (Stacks 06Z0), which is perfect (Stacks 08EB), hence
represented by a bounded complex of finite projective modules.

## Main results

* `AlgebraicGeometry.Space.exists_finiteProjective_representedTilde_iso_of_isPerfect`.

## References

* [Stacks Project, Tag 08HG](https://stacks.math.columbia.edu/tag/08HG)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 09RJ](https://stacks.math.columbia.edu/tag/09RJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance]
  _root_.AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModule

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
  (p : Spec (CommRingCat.of A) ⟶ S)

/-- **A perfect object of `D(𝒪_{h_{Spec A}})` is a bounded complex of finite projective
`A`-modules.** Every perfect object `E` on the small étale site of the algebraic space represented
by `Spec A` is isomorphic to the image of a bounded complex of finite projective `A`-modules under
the termwise functor `M ↦ ε^*(M̃)`. -/
theorem exists_finiteProjective_representedTilde_iso_of_isPerfect
    (E : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj (BigFppfOver.mk B S hS hA p))
      (isAlgebraicSpace_yoneda B S hS _)))
    (hE : (smallEtaleRingedSite B S hS (yoneda.obj (BigFppfOver.mk B S hS hA p))
      (isAlgebraicSpace_yoneda B S hS _)).IsPerfect E) :
    ∃ C : CochainComplex (ModuleCat.{u} A) ℤ, {i : ℤ | ¬ IsZero (C.X i)}.Finite ∧
      (∀ i : ℤ, Module.Finite A (C.X i)) ∧ (∀ i : ℤ, Module.Projective A (C.X i)) ∧
      Nonempty (DerivedCategory.Q.obj
        (((representedTilde B S hS hA p).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) ≅
          E) := by
  let T := BigFppfOver.mk B S hS hA p
  have hq := derivedCategoryB_isQuasicoherentOnSite_of_isPerfect_of_isAlgebraicSpace B S hS
    (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) E hE
  obtain ⟨N, hNq, ⟨eN⟩⟩ := exists_representedDerivedAssociatedModule_iso B S hS T E hq
  have hN : Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (Spec (CommRingCat.of A)).toRingedSpace) N := by
    refine isPerfect_of_isPerfect_representedDerivedAssociatedModule_of_scheme B S hS T N hNq ?_
    obtain ⟨E', hE', ⟨e⟩⟩ := hE
    exact ⟨E', hE', ⟨e ≪≫ eN.symm⟩⟩
  obtain ⟨M, ⟨eM⟩⟩ := AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory
    (CommRingCat.of A) N
    (AlgebraicGeometry.PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ N hN)
  have hM : StacksDraft.Perfect.IsPerfect M :=
    (isPerfect_tilde_iff M).1
      (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
        (X := (Spec (CommRingCat.of A)).toRingedSpace) eM.symm hN)
  obtain ⟨C, a, b, ha, hb, hfin, hproj, ⟨eC⟩⟩ := hM
  have hbd : {i : ℤ | ¬ IsZero (C.X i)}.Finite := by
    refine Set.Finite.subset (Set.finite_Icc a b) fun i hi => ?_
    simp only [Set.mem_ofPred_eq] at hi
    refine Set.mem_Icc.2 ⟨?_, ?_⟩ <;> by_contra hcon
    · exact hi (C.isZero_of_isStrictlyGE a i (by lia))
    · exact hi (C.isZero_of_isStrictlyLE b i (by lia))
  let ε : (Spec (CommRingCat.of A)).Modules ⥤
      Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) :=
    representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)
  have : PreservesFiniteColimits (tilde.functor (CommRingCat.of A)) :=
    Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor (CommRingCat.of A)
  have : (tilde.functor (CommRingCat.of A)).Additive := ⟨tilde.map_add _ _⟩
  have : PreservesFiniteLimits (tilde.functor (CommRingCat.of A)) :=
    AlgebraicGeometry.tilde.preservesFiniteLimits _
  have : ε.Additive := additive_representedAssociatedModule B S hS T _
  have : PreservesFiniteColimits ε :=
    preservesFiniteColimits_representedAssociatedModule B S hS T _
  have : PreservesFiniteLimits ε := preservesFiniteLimits_representedAssociatedModule B S hS T _
  have : (representedAssociatedModule B S hS (BigFppfOver.mk B S hS hA p)
      (isAlgebraicSpace_yoneda B S hS _)).Additive :=
    additive_representedAssociatedModule B S hS _ _
  have : PreservesFiniteColimits (representedAssociatedModule B S hS (BigFppfOver.mk B S hS hA p)
      (isAlgebraicSpace_yoneda B S hS _)) :=
    preservesFiniteColimits_representedAssociatedModule B S hS _ _
  have : PreservesFiniteLimits (representedAssociatedModule B S hS (BigFppfOver.mk B S hS hA p)
      (isAlgebraicSpace_yoneda B S hS _)) :=
    preservesFiniteLimits_representedAssociatedModule B S hS _ _
  refine ⟨C, hbd, hfin, hproj, ⟨?_⟩⟩
  exact DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso (F := tilde.functor (CommRingCat.of A)) (G := ε)
        (Iso.refl (representedTilde B S hS hA p))
        (ComplexShape.up ℤ)).app C).symm ≪≫
    (ε.mapDerivedCategoryFactors.app _).symm ≪≫
    ε.mapDerivedCategory.mapIso
      ((((tilde.functor (CommRingCat.of A)).mapDerivedCategoryFactors).app C).symm ≪≫
        (tilde.functor (CommRingCat.of A)).mapDerivedCategory.mapIso eC.symm ≪≫ eM) ≪≫ eN

end AlgebraicGeometry.Space

end

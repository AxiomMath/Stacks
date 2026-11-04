module

public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedSheafHomSliceModel
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.SliceAffineDualAmplitude
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.Comparison
public import StacksFrontier.Homology.PseudoCoherentRelative.StrictlyPerfectRestrict
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.RingedSiteComparison

/-!
# Coherence of the transport from a slice site, at a strictly perfect complex and at a cone

Let `X` be a locally Noetherian scheme and `W ⊆ X` an affine open. The two amplitude bounds of
`Stacks.Duality.exists_forall_isLE_derivedSheafHomSlice` and its companion ask for coherence of
the cohomology sheaves of the *transport* `Stacks.Duality.sliceSpecFunctor W hW` of an object of
the derived category of `𝒪_X|_W`-modules on `Opens(X)/W`, an object of `D(𝒪_{Spec Γ(X, W)})`.
The dévissage behind the evaluation isomorphism of [Stacks, Tag 0A69] applies those bounds to two
objects born on the slice site: the class of a strictly perfect complex, and the cone of a
morphism out of one. This file supplies the coherence of the transport of both.

## Main results

* `Stacks.Duality.isCoherent_homology_sliceSpecFunctor_Q_of_isStrictlyPerfect`: the transport of
  the class of a strictly perfect complex has coherent cohomology sheaves.
* `Stacks.Duality.isCoherent_homology_obj₃_of_distinguished`: on a scheme, two out of three in a
  distinguished triangle for coherence of all cohomology sheaves, at the third vertex — in
  particular at the cone of a morphism.
* `Stacks.Duality.isCoherent_homology_sliceSpecFunctor_obj₃_of_distinguished`: the same read
  through the transport, which is what reaches the cone of a strictly perfect approximation.

## The proofs

**The strictly perfect complex.** Coherence of the cohomology of a strictly perfect complex is
available over a locally Noetherian scheme
(`Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_homology_of_isStrictlyPerfect`) and on an
arbitrary site with coherent unit
(`Stacks.SheafOfModules.Site.isCoherent_homology_of_isStrictlyPerfect`). It is the first of the
two that is used, because the conclusion wanted here is about `Spec Γ(X, W)`: what travels is not
the coherence but the strict perfection. Each factor of the transport is exact and carries the
structure sheaf to the structure sheaf — `Stacks.SheafOfModules.overEquivUnitIso` for
`AlgebraicGeometry.Scheme.Modules.overEquiv` and Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictUnitIso` for the restriction along an isomorphism of
schemes — so `Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex` carries the complex
across, and `AlgebraicGeometry.RingedSpace.PseudoCoherence.isStrictlyPerfect_iff` reads the
result at the ringed-space spelling the coherence statement is given at. The class of the
transported complex is the transport of the class because each factor is exact
(`CategoryTheory.Functor.mapDerivedCategoryFactors`).

**The cone.** Coherent modules on a scheme are a weak Serre subcategory
(`Stacks.AlgebraicGeometry.ProperSupportCoherent.isCoherent_isWeakSerre`), so having all
cohomology sheaves coherent is two-out-of-three in a distinguished triangle
(`StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory`); rotating puts the cone in the
middle. Both factors of the transport are induced on unbounded derived categories by an exact
functor, hence triangulated, so a distinguished triangle of the slice site is carried to a
distinguished triangle of `D(𝒪_{Spec Γ(X, W)})`.

## Implementation notes

The additivity of `AlgebraicGeometry.Scheme.Modules.overEquiv` is passed to
`Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex` as a *term*, through an explicit
`@`-application, for the reason recorded in
`StacksFrontier/Homology/PseudoCoherentRelative/StrictlyPerfectRestrict.lean`: that statement is
phrased for a functor between two `SheafOfModules` categories, while the instance is declared at
the `AlgebraicGeometry.Scheme.Modules` spelling of the target, and `Scheme.Modules` is a
semireducible `def` that instance search will not unfold. A type ascription is checked at default
transparency, where the two spellings are interchangeable.

## References

* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 0A69](https://stacks.math.columbia.edu/tag/0A69)
* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open Opposite AlgebraicGeometry

universe u

-- Standard model only: `Stacks.AlgebraicGeometry.ProperSupportCoherent.isCoherent_isWeakSerre`.
attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.Duality

variable {X : Scheme.{u}}

/-! ### The class of a strictly perfect complex -/

/-- **The transport of the class of a strictly perfect complex has coherent cohomology sheaves.**
Let `X` be a locally Noetherian scheme, `W ⊆ X` an affine open and `P` a strictly perfect complex
of `𝒪_X|_W`-modules on `Opens(X)/W` ([Stacks, Tag 08FL]). Then every cohomology sheaf of the
transport `Stacks.Duality.sliceSpecFunctor W hW` of the class of `P` is a coherent
`𝒪_{Spec Γ(X, W)}`-module.

What travels is the strict perfection, not the coherence: each factor of the transport is exact
and carries the structure sheaf to the structure sheaf, so it carries `P` to a strictly perfect
complex over `Spec Γ(X, W)`, whose cohomology is coherent because `Spec Γ(X, W)` is locally
Noetherian. -/
theorem isCoherent_homology_sliceSpecFunctor_Q_of_isStrictlyPerfect [IsLocallyNoetherian X]
    (W : X.Opens) (hW : IsAffineOpen W)
    {P : CochainComplex (SheafOfModules.{u} (X.ringCatSheaf.over W)) ℤ}
    (hP : IsStrictlyPerfect (X.ringCatSheaf.over W) P) (n : ℤ) :
    ((DerivedCategory.homologyFunctor (Spec Γ(X, W)).Modules n).obj
      ((sliceSpecFunctor W hW).obj (DerivedCategory.Q.obj P))).IsCoherent := by
  let : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have : IsLocallyNoetherian (Spec Γ(X, W)) := isLocallyNoetherian_Spec.mpr ‹_›
  have hAdd : ((Scheme.Modules.overEquiv W).functor).Additive :=
    Stacks.SheafOfModules.overEquivFunctorAdditive W
  have hCol : PreservesFiniteColimits ((Scheme.Modules.overEquiv W).functor) := inferInstance
  have hP₁ := @Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex
    _ _ _ _ _ _ _ _ _ _ _ _ ((Scheme.Modules.overEquiv W).functor) hAdd hCol
    (Stacks.StalkFreeBridge.overEquivUnitIso W) P hP
  have hP₁' : StrictlyPerfect.IsStrictlyPerfect (X := W.toScheme.toRingedSpace)
      (((Scheme.Modules.overEquiv W).functor.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) :=
    (AlgebraicGeometry.RingedSpace.PseudoCoherence.isStrictlyPerfect_iff
      W.toScheme.toRingedSpace _).2 hP₁
  have hP₂ := Scheme.Modules.isStrictlyPerfect_restrictFunctor hW.isoSpec.inv hP₁'
  have hcoh := Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_homology_of_isStrictlyPerfect
    (Spec Γ(X, W)) _ hP₂ n
  have eQ : (sliceSpecFunctor W hW).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        (((Scheme.Modules.restrictFunctor hW.isoSpec.inv).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
            (((Scheme.Modules.overEquiv W).functor.mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) :=
    (Scheme.Modules.restrictFunctor hW.isoSpec.inv).mapDerivedCategory.mapIso
        (((Scheme.Modules.overEquiv W).functor).mapDerivedCategoryFactors.app P) ≪≫
      ((Scheme.Modules.restrictFunctor hW.isoSpec.inv)).mapDerivedCategoryFactors.app _
  exact AlgebraicGeometry.isCoherent_of_modulesIso
    (((DerivedCategory.homologyFunctorFactors (Spec Γ(X, W)).Modules n).app _).symm ≪≫
      (DerivedCategory.homologyFunctor (Spec Γ(X, W)).Modules n).mapIso eQ.symm)
    hcoh.rootIsCoherent

/-! ### The cone of a morphism -/

/-- **Having all cohomology sheaves coherent is two out of three in a distinguished triangle, at
the third vertex.** In particular the cone of a morphism of `D(𝒪_Y)` between objects of
`D_Coh(𝒪_Y)` lies in `D_Coh(𝒪_Y)`: rotating the triangle puts the cone in the middle, with the
shift of the first vertex third, and coherent `𝒪_Y`-modules are a weak Serre subcategory. -/
theorem isCoherent_homology_obj₃_of_distinguished {Y : Scheme.{u}}
    (T : Triangle (DerivedCategory Y.Modules)) (hT : T ∈ distTriang _)
    (h₁ : ∀ n : ℤ, ((DerivedCategory.homologyFunctor Y.Modules n).obj T.obj₁).IsCoherent)
    (h₂ : ∀ n : ℤ, ((DerivedCategory.homologyFunctor Y.Modules n).obj T.obj₂).IsCoherent)
    (n : ℤ) : ((DerivedCategory.homologyFunctor Y.Modules n).obj T.obj₃).IsCoherent :=
  DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished
    (fun M : Y.Modules => M.IsCoherent)
    (Stacks.AlgebraicGeometry.ProperSupportCoherent.isCoherent_isWeakSerre Y)
    T.rotate (rot_of_distTriang T hT) h₂
    (DerivedCategoryB.derivedCategoryB_shift_mem (fun M : Y.Modules => M.IsCoherent)
      (Stacks.AlgebraicGeometry.ProperSupportCoherent.isCoherent_isWeakSerre Y) 1 h₁) n

/-- **Coherence of the transport is two out of three in a distinguished triangle of the slice
site, at the third vertex.** Both factors of `Stacks.Duality.sliceSpecFunctor` are induced on
unbounded derived categories by an exact functor, hence triangulated, so a distinguished triangle
of `D(𝒪_X|_W)` on `Opens(X)/W` is carried to a distinguished triangle of
`D(𝒪_{Spec Γ(X, W)})`, where `Stacks.Duality.isCoherent_homology_obj₃_of_distinguished`
applies.

This is what supplies the coherence hypothesis of the two amplitude bounds at the cone of a
strictly perfect approximation, an object that exists on the slice site and nowhere else. -/
theorem isCoherent_homology_sliceSpecFunctor_obj₃_of_distinguished [IsLocallyNoetherian X]
    (W : X.Opens) (hW : IsAffineOpen W)
    (T : Triangle (DerivedCategory (SheafOfModules.{u} (X.ringCatSheaf.over W))))
    (hT : T ∈ distTriang _)
    (h₁ : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (Spec Γ(X, W)).Modules i).obj
      ((sliceSpecFunctor W hW).obj T.obj₁)).IsCoherent)
    (h₂ : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (Spec Γ(X, W)).Modules i).obj
      ((sliceSpecFunctor W hW).obj T.obj₂)).IsCoherent) (i : ℤ) :
    ((DerivedCategory.homologyFunctor (Spec Γ(X, W)).Modules i).obj
      ((sliceSpecFunctor W hW).obj T.obj₃)).IsCoherent :=
  isCoherent_homology_obj₃_of_distinguished _
    ((Scheme.Modules.restrictFunctor hW.isoSpec.inv).mapDerivedCategory.map_distinguished
      _ (((Scheme.Modules.overEquiv W).functor).mapDerivedCategory.map_distinguished T hT))
    h₁ h₂ i

end Stacks.Duality

end

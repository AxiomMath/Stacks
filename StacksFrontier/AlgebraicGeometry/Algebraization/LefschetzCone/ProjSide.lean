module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjQuasicoherent.Isomorphism
public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.TorsionVanishing
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Exact
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.GradedQuotients
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjGradedRing.Basic
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicPro
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzCone.ChartSections

/-!
# Graded modules over the section ring as modules on the projective scheme

Let `X` be a scheme with an ample invertible `𝒪_X`-module `L`, let `A = Γ_*(X, L)` be its graded
section ring and `f : X ⟶ Proj A` the canonical morphism of Stacks 01PZ. Pulling back the sheaf
associated to a graded module along `f` is the functor

`Φ : M ↦ f^* M̃`

from graded `A`-modules to quasi-coherent `𝒪_X`-modules. This file records the two properties of
`Φ` that the last step of the proof of Stacks 0EL5 uses:

* `Φ` inverts every map with `A₊`-power torsion kernel and cokernel, because `M ↦ M̃` is exact
  (Stacks 01M7) and kills the `A₊`-power torsion modules (the first step of Stacks 0BXD);
* `Φ(Γ_*(X, L, ℱ)) ≅ ℱ` naturally in the quasi-coherent module `ℱ`, which is Stacks 01QJ.

## Main definitions

* `Stacks.LefschetzCone.sheafFunctor`: the functor `Φ`, into quasi-coherent `𝒪_X`-modules.

## Main results

* `Stacks.LefschetzCone.isIso_associatedModuleSheafFunctor_map`: `M ↦ M̃` inverts the maps with
  `A₊`-power torsion kernel and cokernel, for any graded ring.
* `Stacks.LefschetzCone.isInvertedBy_sheafFunctor`: so does `Φ`.
* `Stacks.LefschetzCone.sheafFunctorTwistedSectionsIso`: `Φ(Γ_*(X, L, ℱ)) ≅ ℱ`, for an inverse
  system of quasi-coherent modules.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AmpleFiniteAvoidance (grading)
open Stacks.SectionRingProjMorphism (projHomOfIsAmple)
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open scoped Stacks.GradedLocalization

universe u w

namespace Stacks.LefschetzCone

/-! ### `M ↦ M̃` inverts the maps that are isomorphisms modulo torsion -/

section Torsion

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local instance] preservesFiniteLimits_associatedModuleSheafFunctor
  preservesFiniteColimits_associatedModuleSheafFunctor

/-- **`M ↦ M̃` inverts a map with `S₊`-power torsion kernel and cokernel.** The functor is exact,
so it carries the kernel and the cokernel of the map to those of its image; and it kills
`S₊`-power torsion modules. A map of sheaves of modules with zero kernel and zero cokernel is an
isomorphism. -/
public theorem isIso_associatedModuleSheafFunctor_map {M N : GradedModuleCat.{u, u, w} 𝒮}
    (φ : M ⟶ N) (hφ : (GradedModuleCat.isoModTorsion 𝒮
      (HomogeneousIdeal.irrelevant 𝒮).toIdeal) φ) :
    IsIso ((associatedModuleSheafFunctor 𝒮).map φ) := by
  obtain ⟨hker, hcoker⟩ := hφ
  let F := associatedModuleSheafFunctor.{u, u, w} 𝒮
  have hmono : Mono (F.map φ) :=
    Preadditive.mono_of_isZero_kernel' _
      (KernelFork.mapIsLimit _ (GradedModuleCat.kernelForkIsLimit φ) F)
      (Stacks.AlgebraicGeometry.ProjSerreCorrespondence.isZero_associatedModuleSheafFunctor_obj
        𝒮 _ hker)
  have hepi : Epi (F.map φ) :=
    Preadditive.epi_of_isZero_cokernel' _
      (CokernelCofork.mapIsColimit _ (GradedModuleCat.cokernelCoforkIsColimit φ) F)
      (Stacks.AlgebraicGeometry.ProjSerreCorrespondence.isZero_associatedModuleSheafFunctor_obj
        𝒮 _ hcoker)
  exact isIso_of_mono_of_epi _

end Torsion

/-! ### The functor `Φ` on the projective scheme -/

section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local instance] ProjectiveSpectrum.isPrime

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (hL : Stacks.Ample.IsAmple X L) [IsOpenImmersion (projHomOfIsAmple L hL)]

/-- The restriction of the sheaf associated to a graded module is quasi-coherent. -/
public theorem isQuasicoherent_restrictedTilde (M : GradedModuleCat.{u, u, u} (grading L)) :
    (restrictedTilde L hL M).IsQuasicoherent := by
  have : ((Stacks.SectionRingProjQuasicoherent.associatedSchemeFunctor L).obj M).IsQuasicoherent :=
    AlgebraicGeometry.associatedModuleSheaf_isQuasicoherent (grading L) M.grade
  exact Scheme.Modules.isQuasicoherent_restrictFunctor _ _

/-- **The functor `Φ : M ↦ f^* M̃ = M̃|_X`** from graded `Γ_*(X, L)`-modules to quasi-coherent
`𝒪_X`-modules, `f : X ⟶ Proj Γ_*(X, L)` the canonical morphism of Stacks 01PZ. -/
public def sheafFunctor :
    GradedModuleCat.{u, u, u} (grading L) ⥤ Scheme.QuasicoherentModules X :=
  ObjectProperty.lift _ (restrictedTildeFunctor L hL) (isQuasicoherent_restrictedTilde L hL)

/-- **`Φ` inverts the maps with `A₊`-power torsion kernel and cokernel.** -/
public theorem isInvertedBy_sheafFunctor :
    (GradedModuleCat.isoModTorsion (grading L)
      (HomogeneousIdeal.irrelevant (grading L)).toIdeal).IsInvertedBy (sheafFunctor L hL) := by
  intro M N φ hφ
  have h : IsIso ((Stacks.SectionRingProjQuasicoherent.associatedSchemeFunctor L).map φ) :=
    isIso_associatedModuleSheafFunctor_map (grading L) φ hφ
  have h' : IsIso ((Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL)).map
      ((Stacks.SectionRingProjQuasicoherent.associatedSchemeFunctor L).map φ)) :=
    Functor.map_isIso _ _
  exact (ObjectProperty.isIso_hom_iff _).mp h'

/-- **`(Γ_*(X, L, ℱ))~|_X ≅ ℱ`** on quasi-coherent modules, naturally in `ℱ`: the comparison of
Stacks 01QJ restricted to the quasi-coherent modules, where every component is an isomorphism. -/
public def restrictedTildeTwistedSectionsIso :
    ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        (Stacks.SectionRingProjQuasicoherent.tildeFunctor L ⋙
          Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL)) ≅
      ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) :=
  @asIso _ _ _ _ (Functor.whiskerLeft _
      (Stacks.SectionRingProjQuasicoherent.gluedComparisonNatTrans L hL))
    (@NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun F => by
      have : F.obj.IsQuasicoherent := F.property
      exact Stacks.SectionRingProjQuasicoherent.isIso_gluedComparison L hL F.obj)

/-- **`Φ(Γ_*(X, L, ℱₙ)) ≅ ℱₙ`** for an inverse system of quasi-coherent modules, naturally in `n`:
the isomorphism of Stacks 01QJ, applied termwise, as an isomorphism of inverse systems of
`𝒪_X`-modules. -/
public def sheafFunctorTwistedSectionsIso (F : ℕᵒᵖ ⥤ Scheme.QuasicoherentModules X) :
    ((F ⋙ ObjectProperty.ι _ ⋙
      Stacks.SectionRingProjQuasicoherent.gradedTwistedSectionsFunctor L) ⋙ sheafFunctor L hL) ⋙
        ObjectProperty.ι _ ≅ F ⋙ ObjectProperty.ι _ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (ObjectProperty.liftCompιIso _ _ _) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
      restrictedTildeTwistedSectionsIso L hL)

end Monoidal

end Stacks.LefschetzCone

end

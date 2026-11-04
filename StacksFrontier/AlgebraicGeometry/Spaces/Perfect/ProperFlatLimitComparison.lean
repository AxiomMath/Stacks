module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CoheratorLimitComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointPerfectOfProper

/-!
# The canonical map of Stacks 0D3F for proper flat morphisms of finite presentation

Let `f : X ⟶ T` be proper, flat and of finite presentation with `T = Spec R` affine, and let
`(M_n)` be an inverse system of `R`-modules with surjective transition maps. The proof of
Stacks 0D3F needs `RΓ(X, -)` to carry perfect objects to perfect objects (Stacks 0CTM); on the
spaces-étale model this is
`AlgebraicGeometry.Space.isPerfect_derivedPushforward_spacesEtaleModelToBaseRing_of_isProper`,
whose one input is the descent of perfect objects along approximating systems (the essential
surjectivity half of Stacks 09RJ). This file feeds it into the two forms of Stacks 0D3F.

## Main results

* `AlgebraicGeometry.Space.bijective_comp_single_limitComparison_baseRingTensorModule_of_isProper`:
  composition with `𝒪_X ⊗_R lim M_n ⟶ lim 𝒪_X ⊗_R M_n` in degree zero is bijective on maps out
  of every object of `D_QCoh(𝒪_X)`.
* `AlgebraicGeometry.Space.isIso_coherator_map_single_limitComparison_of_isProper`: `DQ_X`
  inverts that map.

## References

* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
* [Stacks Project, Tag 09RJ](https://stacks.math.columbia.edu/tag/09RJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard
attribute [-instance] SheafOfModules.hasColimitsOfShape_discrete_derivedCategory
attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}

/-- **The canonical map of Stacks 0D3F, for `f` proper, flat and of finite presentation, given
the descent of perfect objects.** Let `f : X ⟶ T` be proper, flat and of finite presentation over
an affine `T` with `R = Γ(T, 𝒪_T)`, and let `(M_n)` be an inverse system of `R`-modules with
surjective transition maps. If perfect objects descend along approximating systems over `Spec ℤ`
(`hdescent`, the essential surjectivity half of Stacks 09RJ), then composition with the canonical
map `𝒪_X ⊗_R lim M_n ⟶ lim 𝒪_X ⊗_R M_n`, placed in degree zero, is bijective on maps out of every
object of `D_QCoh(𝒪_X)`. -/
theorem bijective_comp_single_limitComparison_baseRingTensorModule_of_isProper
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hdescent : ∀ (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I), ChartsBounded B _ hZ D.system →
      ∀ E : DerivedCategory (spacesEtaleModelRingedTopos B _ hZ
          ⟨D.limitCone.pt, D.limitAlgebraicSpace⟩).Modules,
        (spacesEtaleModelRingedTopos B _ hZ
          ⟨D.limitCone.pt, D.limitAlgebraicSpace⟩).toRingedSite.IsPerfect E →
        ∃ (i : I) (_ : D.base ≤ i) (Eᵢ : DerivedCategory (spacesEtaleModelRingedTopos B _ hZ
            ⟨D.system.obj (op i), D.algebraicSpace i⟩).Modules),
          (spacesEtaleModelRingedTopos B _ hZ
            ⟨D.system.obj (op i), D.algebraicSpace i⟩).toRingedSite.IsPerfect Eᵢ ∧
          Nonempty ((derivedPullback (spacesEtaleModelHom B _ hZ
            (ObjectProperty.homMk (D.limitCone.π.app (op i)) :
              (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B _ hZ) ⟶
                ⟨D.system.obj (op i), D.algebraicSpace i⟩))).obj Eᵢ ≅ E))
    (f : X ⟶ schemeSpace T) (hf : IsProper B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (Msys : ℕᵒᵖ ⥤ ModuleCat.{u} (baseRing B S hS T))
    (hsurj : ∀ n : ℕ, Function.Surjective (Msys.map (homOfLE (Nat.le_succ n)).op))
    [HasProduct fun n : ℕ =>
      (baseRingTensorModule B S hS X (baseRingHomOfMap f)).obj (Msys.obj ⟨n⟩)]
    [HasLimit (Msys ⋙ baseRingTensorModule B S hS X (baseRingHomOfMap f))]
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hE : qcohDerivedProp B S hS X E) :
    Function.Bijective
      (fun a : E ⟶ (DerivedCategory.singleFunctor _ 0).obj
          ((baseRingTensorModule B S hS X (baseRingHomOfMap f)).obj (limit Msys)) =>
        a ≫ (DerivedCategory.singleFunctor _ 0).map
          (limit.post Msys (baseRingTensorModule B S hS X (baseRingHomOfMap f)))) :=
  bijective_comp_single_limitComparison_baseRingTensorModule_of_isPerfect_derivedPushforward hZ f
    hflat hfp hT Msys hsurj
    (isPerfect_derivedPushforward_spacesEtaleModelToBaseRing_of_isProper hZ hdescent
      hT f hf hfp hflat)
    E hE

/-- **`DQ_X` inverts the canonical map of Stacks 0D3F, for `f` proper, flat and of finite
presentation, given the descent of perfect objects.** Let `f : X ⟶ T` be proper, flat and of
finite presentation over an affine `T`, and let `(M_n)` be an inverse system of
`Γ(T, 𝒪_T)`-modules with surjective transition maps. If perfect objects descend along
approximating systems over `Spec ℤ` (`hdescent`, the essential surjectivity half of Stacks 09RJ)
and `φ : 𝒢 ⟶ 𝒩` is, up to isomorphisms `𝒢 ≅ 𝒪_X ⊗ lim M_n` and `lim 𝒪_X ⊗ M_n ≅ 𝒩`, the
canonical map `𝒪_X ⊗ lim M_n ⟶ lim 𝒪_X ⊗ M_n`, then `DQ_X` applied to `φ` in degree zero is an
isomorphism. -/
theorem isIso_coherator_map_single_limitComparison_of_isProper
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hdescent : ∀ (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I), ChartsBounded B _ hZ D.system →
      ∀ E : DerivedCategory (spacesEtaleModelRingedTopos B _ hZ
          ⟨D.limitCone.pt, D.limitAlgebraicSpace⟩).Modules,
        (spacesEtaleModelRingedTopos B _ hZ
          ⟨D.limitCone.pt, D.limitAlgebraicSpace⟩).toRingedSite.IsPerfect E →
        ∃ (i : I) (_ : D.base ≤ i) (Eᵢ : DerivedCategory (spacesEtaleModelRingedTopos B _ hZ
            ⟨D.system.obj (op i), D.algebraicSpace i⟩).Modules),
          (spacesEtaleModelRingedTopos B _ hZ
            ⟨D.system.obj (op i), D.algebraicSpace i⟩).toRingedSite.IsPerfect Eᵢ ∧
          Nonempty ((derivedPullback (spacesEtaleModelHom B _ hZ
            (ObjectProperty.homMk (D.limitCone.π.app (op i)) :
              (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B _ hZ) ⟶
                ⟨D.system.obj (op i), D.algebraicSpace i⟩))).obj Eᵢ ≅ E))
    (f : X ⟶ schemeSpace T) (hf : IsProper B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (Msys : ℕᵒᵖ ⥤ ModuleCat.{u} (baseRing B S hS T))
    (hsurj : ∀ n : ℕ, Function.Surjective (Msys.map (homOfLE (Nat.le_succ n)).op))
    [HasProduct fun n : ℕ =>
      (baseRingTensorModule B S hS X (baseRingHomOfMap f)).obj (Msys.obj ⟨n⟩)]
    [HasLimit (Msys ⋙ baseRingTensorModule B S hS X (baseRingHomOfMap f))]
    {G N : Modules.{u, u} B S hS X.1 X.2} (φ : G ⟶ N)
    (α : G ≅ (baseRingTensorModule B S hS X (baseRingHomOfMap f)).obj (limit Msys))
    (β : limit (Msys ⋙ baseRingTensorModule B S hS X (baseRingHomOfMap f)) ≅ N)
    (hφ : φ = α.hom ≫ limit.post Msys (baseRingTensorModule B S hS X (baseRingHomOfMap f)) ≫
      β.hom) :
    letI := quasicoherentDerivedInclusion_isLeftAdjoint_of_qcqs B S hS hZ X.1 X.2
      (qcqs_of_isFinitePresentation_schemeSpace hZ f hT hfp).1
      (qcqs_of_isFinitePresentation_schemeSpace hZ f hT hfp).2
    IsIso ((qcohDerivedProp B S hS X).ι.rightAdjoint.map
      ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).map φ)) :=
  have hq := qcqs_of_isFinitePresentation_schemeSpace hZ f hT hfp
  isIso_coherator_map_single_of_eq_limitComparison hZ hq.1 hq.2 f hflat hfp hT Msys hsurj
    (isPerfect_derivedPushforward_spacesEtaleModelToBaseRing_of_isProper hZ hdescent
      hT f hf hfp hflat)
    φ α β hφ

end AlgebraicGeometry.Space

end

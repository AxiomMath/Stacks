module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwistFlatness
public import StacksFrontier.AlgebraicGeometry.PicardUFD.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveSpaceTwistPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedInvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackInvertible.RingedTopos
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackOfToposHom

/-!
# The twisting modules of projective space on the small étale site

Let `A` be a ring and `P = ℙⁿ_A`. The object `𝒪(d)` of `D(𝒪_P)` of
`AlgebraicGeometry.Space.projectiveSpaceSiteTwist` is a module placed in degree zero: the
pullback, along the isomorphism of the two models of projective space and the comparison `ε` of
Stacks 071Q, of the twisting sheaf `𝒪(d)` of `Proj A[T₀, …, Tₙ]`. That module is flat and
invertible.

## Main definitions

* `AlgebraicGeometry.Space.projectiveSpaceSiteTwistModule`: `𝒪(d)` as an `𝒪_P`-module.

## Main results

* `AlgebraicGeometry.Space.nonempty_projectiveSpaceSiteTwist_iso`: there is an isomorphism
  `𝒪(d) ≅ 𝒪(d)[0]` in `D(𝒪_P)`.
* `AlgebraicGeometry.Space.isFlat_projectiveSpaceSiteTwistModule`,
  `AlgebraicGeometry.Space.isInvertibleModule_projectiveSpaceSiteTwistModule`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable (B : BigFppfSite.{u}) {A : Type u} [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
  (n : ℕ) (hP : B.Contains (projectiveSpaceOver n (Spec (CommRingCat.of A))))

/-- The twisting sheaf `𝒪(d)` of `Proj A[T₀, …, Tₙ]` is flat. -/
theorem isFlat_twistingSheaf_polyGrading (d : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (Proj (polyGrading A n)).zariskiRingedTopos.O)
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) d) :=
  Stacks.SheafOfModules.isFlat_of_isInvertible (X := (Proj (polyGrading A n)).toRingedSpace) _
    (Stacks.PicardUFD.isInvertible_twistingSheaf A n d)

/-- **`𝒪(d)` on the small étale site of `ℙⁿ_A`, as a module**: the twisting sheaf of the model
pulled back along `ε` and the isomorphism of the two models. -/
abbrev projectiveSpaceSiteTwistModule (d : ℤ) :
    SheafOfModules.{u} (ringedToposStructureRingSheaf B _ hA
      (schemeSpace (projectiveSpaceSiteObj B _ hA n hP))) :=
  (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    (X := smallEtaleRingedTopos B _ hA (schemeSpace (projectiveSpaceSiteObj B _ hA n hP)))
    (Y := smallEtaleRingedTopos B _ hA (representedSpace (projModelSiteObj B hA n)))
    (smallEtaleRingedToposHom B _ hA (projModelSpaceIso B hA n hP).inv).toModulesHom).obj
    ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B _ hA
        (projModelSiteObj B hA n)).obj
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) d))

/-- `ε^*𝒪(d)` is flat on the small étale site of the model. -/
theorem isFlat_representedZariskiModulePullback_twistingSheaf (d : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B _ hA (representedSpace (projModelSiteObj B hA n))).O)
      ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B _ hA
          (projModelSiteObj B hA n)).obj
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) d)) :=
  Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isFlat_pullbackModules_obj
    (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B _ hA
      (projModelSiteObj B hA n)) _
    (isFlat_twistingSheaf_polyGrading n d)

/-- **`𝒪(d)` on `ℙⁿ_A` is a flat module.** -/
theorem isFlat_projectiveSpaceSiteTwistModule (d : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B _ hA
        (schemeSpace (projectiveSpaceSiteObj B _ hA n hP))).O)
      (projectiveSpaceSiteTwistModule B hA n hP d) :=
  Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isFlat_pullbackModules_obj
    (smallEtaleRingedToposHom B _ hA (projModelSpaceIso B hA n hP).inv) _
    (isFlat_representedZariskiModulePullback_twistingSheaf B hA n d)

/-- `ε^*𝒪(d)` is invertible on the small étale site of the model (Stacks 0B8P). -/
theorem isInvertibleModule_representedZariskiModulePullback_twistingSheaf (d : ℤ) :
    IsInvertibleModule (representedSpace (projModelSiteObj B hA n))
      ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B _ hA
          (projModelSiteObj B hA n)).obj
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) d)) := by
  have : Stacks.SheafOfModules.IsInvertible
      (representedSchemeRepresentedZariskiRingedToposHom B _ hA
        (projModelSiteObj B hA n)).zariskiRingedTopos.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (representedSchemeRepresentedZariskiRingedToposHom B _ hA
          (projModelSiteObj B hA n)).zariskiRingedTopos.O).property
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) d) :=
    Stacks.PicardUFD.isInvertible_twistingSheaf A n d
  exact Stacks.SheafOfModules.isInvertible_pullbackModules_obj
    (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B _ hA
      (projModelSiteObj B hA n)).toModulesHom _

/-- **`𝒪(d)` on `ℙⁿ_A` is an invertible module** (Stacks 0B8P). -/
theorem isInvertibleModule_projectiveSpaceSiteTwistModule (d : ℤ) :
    IsInvertibleModule (schemeSpace (projectiveSpaceSiteObj B _ hA n hP))
      (projectiveSpaceSiteTwistModule B hA n hP d) := by
  have := isInvertibleModule_representedZariskiModulePullback_twistingSheaf B hA n d
  exact Stacks.SheafOfModules.isInvertible_pullbackModules_obj
    (smallEtaleRingedToposHom B _ hA (projModelSpaceIso B hA n hP).inv).toModulesHom _

section Derived

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 5000] isGrothendieckAbelian_ringedToposStructureRingSheaf

/-- **`𝒪(d)` on `ℙⁿ_A` is a module placed in degree zero**:
`AlgebraicGeometry.Space.projectiveSpaceSiteTwist` is
`AlgebraicGeometry.Space.projectiveSpaceSiteTwistModule` in degree `0`. -/
theorem nonempty_projectiveSpaceSiteTwist_iso (d : ℤ) :
    Nonempty (projectiveSpaceSiteTwist B hA n hP d ≅
      (DerivedCategory.singleFunctor _ 0).obj (projectiveSpaceSiteTwistModule B hA n hP d)) :=
  ⟨(smallEtaleDerivedModulePullback B _ hA (projModelSpaceIso B hA n hP).inv).mapIso
      ((representedZariskiDerivedPullbackIso B _ hA (projModelSiteObj B hA n)).app _ ≪≫
        ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B _ hA
          (projModelSiteObj B hA n)).mapDerivedCategorySingleFunctor 0).app
            (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) d)) ≪≫
    smallEtaleDerivedModulePullbackSingleIsoOfFlat (projModelSpaceIso B hA n hP).inv _ 0
      (isFlat_representedZariskiModulePullback_twistingSheaf B hA n d)⟩

end Derived

end AlgebraicGeometry.Space

end

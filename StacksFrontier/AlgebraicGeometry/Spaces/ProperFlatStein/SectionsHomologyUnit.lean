module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStein.FibreBettiInputs
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatDerivedPushforwardSplitting

/-!
# Degree-zero cohomology of `Rq_* 𝒪` when `q_* 𝒪 = 𝒪`

Let `T` be an object of the big fppf site with affine scheme and ring `R = Γ(T, 𝒪)`, and let
`q : Q ⟶ h_T` be a quasi-compact and quasi-separated morphism of algebraic spaces whose structure
map `𝒪_T ⟶ q_* 𝒪_Q` is an isomorphism. Then `H⁰(RΓ(T, Rq_* 𝒪_Q)) ≅ R` as `R`-modules.

## Main results

* `AlgebraicGeometry.Space.ProperFlatStein.finrank_baseChangeSectionsHomology_zero_eq_one`:
  the degree-zero Betti number of the base change of `𝒪_X` to an affine `T` is one when the
  structure map of the base change is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules

universe u v w

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space.ProperFlatStein


variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

/-- **`H⁰(RΓ(T, Rq_* 𝒪_Q)) ≅ Γ(T, q_* 𝒪_Q)`** over an affine `T`, for `q` quasi-compact and
quasi-separated, `𝒪_Q` entering through a module `F` with `F ≅ 𝒪_Q`; the sections are those of
`AlgebraicGeometry.Space.representedAffineSections`. -/
def homologyZeroIsoRepresentedSections (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] {Q : AlgebraicSpaces B S hS}
    (q : Q ⟶ ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
    (hqc : IsQuasiCompact B S hS q.hom) (hqs : IsQuasiSeparated B S hS q.hom)
    (F : Modules.{u, u} B S hS Q.1 Q.2) (eF : F ≅ structureModule Q) :
    (@DerivedCategory.homologyFunctor (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
        _ _ (HasDerivedCategory.standard _) 0).obj
      ((representedAffineDerivedSections B S hS T).obj
        ((derivedModulePushforward B S hS q).obj
          ((@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard _) 0).obj F))) ≅
      (representedAffineSections B S hS T).obj
        ((modulePushforward B S hS q).obj (structureModule Q)) :=
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS Q.1 Q.2)
  letI := HasDerivedCategory.standard
    (Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
  letI := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
  (DerivedCategory.homologyFunctor _ 0).mapIso
      ((representedAffineDerivedSections B S hS T).mapIso
        ((derivedModulePushforward B S hS q).mapIso
          ((DerivedCategory.singleFunctor _ 0).mapIso eF))) ≪≫
    representedAffineDerivedSectionsHomologyIso B S hS T _
      (qcohDerived_derivedModulePushforward_obj B S hS q hqc hqs _
        (qcohDerived_singleFunctor_structureModule (B := B) (S := S) (hS := hS) (X := Q.1)
          (hX := Q.2))) 0 ≪≫
    (representedAffineSections B S hS T).mapIso
      ((derivedModulePushforwardSingleHomologyZeroIso B S hS q).app (structureModule Q))

/-- **`H⁰(RΓ(T, Rq_* 𝒪_Q)) ≅ Γ(T, 𝒪)`** over an affine `T`, for `q` quasi-compact and
quasi-separated with `𝒪_T ⟶ q_* 𝒪_Q` an isomorphism. -/
def homologyZeroIsoOfIsIsoStructureSharp (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] {Q X : AlgebraicSpaces B S hS}
    (q : Q ⟶ ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩) (φ : Q ⟶ X)
    (hqc : IsQuasiCompact B S hS q.hom) (hqs : IsQuasiSeparated B S hS q.hom)
    [IsIso (structureSharp B S hS q)] :
    (@DerivedCategory.homologyFunctor (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
        _ _ (HasDerivedCategory.standard _) 0).obj
      ((representedAffineDerivedSections B S hS T).obj
        ((derivedModulePushforward B S hS q).obj
          ((@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard _) 0).obj
            ((modulePullback B S hS φ).obj (structureModule X))))) ≅
      ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
  homologyZeroIsoRepresentedSections B S hS T q hqc hqs _ (modulePullbackUnitIso B S hS φ) ≪≫
    (representedAffineSections B S hS T).mapIso
      ((structureModuleIsoModulePushforward B S hS q).symm ≪≫
        (representedAffineAssociatedObjUnitIso B S hS T).symm) ≪≫
    (asIso ((representedAffineAssociatedAdjunction B S hS T).unit.app _)).symm

/-- The degree-zero Betti number of the base change of `𝒪_X` to an affine `T` over `U` is one
when the structure map of the base change `X ×_U T ⟶ T` is an isomorphism and `Γ(T, 𝒪)` is a
nonzero ring. -/
theorem finrank_baseChangeSectionsHomology_zero_eq_one {U : BigFppfOver B S hS}
    {X : AlgebraicSpaces B S hS} (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
    {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [Nontrivial Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)] (t : T ⟶ U)
    (hqc : IsQuasiCompact B S hS (pullback.snd f (representedSpaceMap B S hS t)).hom)
    (hqs : IsQuasiSeparated B S hS (pullback.snd f (representedSpaceMap B S hS t)).hom)
    [IsIso (structureSharp B S hS (pullback.snd f (representedSpaceMap B S hS t)))] :
    Module.finrank Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)
      (baseChangeSectionsHomology f t (structureModule X) 0) = 1 :=
  ((homologyZeroIsoOfIsIsoStructureSharp B S hS T _ _ hqc hqs).toLinearEquiv.finrank_eq).trans
    (Module.finrank_self _)

end AlgebraicGeometry.Space.ProperFlatStein

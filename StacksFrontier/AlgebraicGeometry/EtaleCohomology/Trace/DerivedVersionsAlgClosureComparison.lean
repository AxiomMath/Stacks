module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DerivedVersionsAlgClosure
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusExtensionCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalCompactSupportComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisEquivariantCompactSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareTransComposition

/-!
# The derived versions of Tag 03VM over an arbitrary field: the étale sides are the original ones

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/DerivedVersionsAlgClosure.lean` states the
derived versions of [Stacks, Tag 03VM] over an arbitrary field `k` by reading them on
`X' = X ×_k k'`, `k'` the perfect closure of `k` in `k̄`. This file identifies the étale sides,
after forgetting the Galois action, with the objects defined directly from the original curve
`X` over `k` and the original sheaf `ℱ_ρ`:

* the Galois-equivariant `RΓ_c` computed on `X'` is `RΓ_c(X_{k̄}, ℱ_ρ) = RΓ(X̄_{k̄}, (j_! ℱ_ρ)|)` of
  Remark 03UI (2) for `X` over `k` and its compactification `j : X ⟶ X̄`
  (`AlgebraicGeometry.perfectClosureCompactSupportForgetIso`);
* the Galois-equivariant `RΓ` computed on `X'` is `RΓ(X_{k̄}, ℱ_ρ|_{X_{k̄}})` for `X` over `k`
  (`AlgebraicGeometry.perfectClosureGaloisDerivedSectionsForgetIso`).

The inputs are general:

* `Stacks.EtaleCohomology.fieldBaseChangeExtensionDerivedSectionsIso`: for any scheme `Y` over
  `k` and any tower `k ⊆ k' ⊆ k̄`, `RΓ(Y'_{k̄}, (g⁻¹ C)|) ≅ RΓ(Y_{k̄}, C|)`, `Y' = Y ×_k k'`;
* `Stacks.EtaleCohomology.galoisCompactSupportCohomologyFieldExtensionIso`: the same for
  `RΓ_c`, with the base-changed compactification (extension by zero commutes with inverse image,
  Tag 03S6);
* `AlgebraicGeometry.perfectClosureModelRepresentationSheafIso`: the sheaf attached on `X'` to
  the restriction of `ρ` is the inverse image of `ℱ_ρ` (Tag 0DV6).

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
* [Stacks Project, Tag 03S6](https://stacks.math.columbia.edu/tag/03S6)
* [Stacks Project, Tag 0DV6](https://stacks.math.columbia.edu/tag/0DV6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.GroupCohomology Stacks.Frobenius Stacks.EtaleCohomology
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

namespace Stacks.EtaleCohomology

section FieldExtension

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k)))
  (k' : Type u) [Field k'] [Algebra k k']
  (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra k' kbar] [IsScalarTower k k' kbar]

/-- **`RΓ(Y'_{k̄}, (g⁻¹ C)|_{Y'_{k̄}}) ≅ RΓ(Y_{k̄}, C|_{Y_{k̄}})`** for a scheme `Y` over `k`, a
tower `k ⊆ k' ⊆ k̄`, `Y' = Y ×_k k'` and `g : Y' ⟶ Y`: both are `RΓ(Spec k̄, -)` of the derived
direct image to `Spec k̄`, which agree by
`Stacks.EtaleCohomology.frobeniusExtensionCohomologyIso`. -/
def fieldBaseChangeExtensionDerivedSectionsIso
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left)) :
    (etaleModuleDerivedGlobalSections.{u, r} Λ (fieldBaseChange (extensionOver Y k') kbar)).obj
        (fieldBaseChangeRestriction.{u, r} Λ (extensionOver Y k') kbar
          ((etaleModuleInverseImage.{u, r} Λ (extensionProj Y k')).mapCochainComplexPlus.obj C)) ≅
      (etaleModuleDerivedGlobalSections.{u, r} Λ (fieldBaseChange Y kbar)).obj
        (fieldBaseChangeRestriction.{u, r} Λ Y kbar C) :=
  (etaleModuleDerivedGlobalSectionsCompIso.{u, r} Λ
      (pullback.snd (extensionOver Y k').hom (specAlgebraMap k' kbar))).app _ ≪≫
    frobeniusExtensionCohomologyIso Λ Y k' kbar C ≪≫
    ((etaleModuleDerivedGlobalSectionsCompIso.{u, r} Λ
      (pullback.snd Y.hom (specAlgebraMap k kbar))).app _).symm

end FieldExtension

section CompactSupport

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f)) (k' : Type u) [Field k']
  [Algebra k k'] (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra k' kbar]
  [IsScalarTower k k' kbar]

/-- **`j'_!(g⁻¹ C) ≅ ḡ⁻¹(j_! C)`** degreewise on a bounded below complex, for the base change
`j' : X ×_k k' ⟶ X̄ ×_k k'` of the compactification `j : X ⟶ X̄` (Tag 03S6). -/
def compactificationExtensionByZeroFieldExtensionComplexIso
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ X)) :
    (etaleModuleExtensionByZero.{u, r} Λ
        (compactificationFieldBaseChange f j k').immersion).mapCochainComplexPlus.obj
        ((etaleModuleInverseImage.{u, r} Λ
          (pullback.fst f (specAlgebraMap k k'))).mapCochainComplexPlus.obj C) ≅
      (etaleModuleInverseImage.{u, r} Λ
          (extensionProj (Over.mk j.toBase) k')).mapCochainComplexPlus.obj
        ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.obj C) :=
  ObjectProperty.isoMk _
    ((NatIso.mapHomologicalComplex
        (etaleModuleInverseImageExtensionByZeroIso.{u, r} Λ
          (isPullback_compactificationFieldBaseChange f j k')) _).app C.obj)

/-- **`RΓ_c(X'_{k̄}, g⁻¹ C) ≅ RΓ_c(X_{k̄}, C)`** in the sense of Remark 03UI (2), for a scheme `X`
over `k` with a compactification `j`, a tower `k ⊆ k' ⊆ k̄`, `X' = X ×_k k'` compactified by the
base change of `j`, and `g : X' ⟶ X`. -/
def galoisCompactSupportCohomologyFieldExtensionIso
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ X)) :
    galoisCompactSupportCohomology.{u, r} Λ (pullback.snd f (specAlgebraMap k k'))
        (compactificationFieldBaseChange f j k') kbar
        ((etaleModuleInverseImage.{u, r} Λ
          (pullback.fst f (specAlgebraMap k k'))).mapCochainComplexPlus.obj C) ≅
      galoisCompactSupportCohomology.{u, r} Λ f j kbar C :=
  (etaleModuleDerivedGlobalSections.{u, r} Λ
      (fieldBaseChange (extensionOver (Over.mk j.toBase) k') kbar)).mapIso
      (DerivedCategory.Plus.Q.mapIso
        ((etaleModuleInverseImage.{u, r} Λ
            (fieldBaseChangeProj (extensionOver (Over.mk j.toBase) k')
              kbar)).mapCochainComplexPlus.mapIso
          (compactificationExtensionByZeroFieldExtensionComplexIso Λ f j k' C))) ≪≫
    fieldBaseChangeExtensionDerivedSectionsIso Λ (Over.mk j.toBase) k' kbar
      ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.obj C)

end CompactSupport

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

/-- The underlying module of a discrete Galois module is a left exact functor (pinned at the module
universe). -/
local instance (priority := 3000) preservesFiniteLimits_galoisModulesUnderlying' (Λ : Type)
    [Ring Λ] {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K] :
    PreservesFiniteLimits
        (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (K ≃ₐ[k] K)) :=
  Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat.{0, u, u + 1} Λ
      (K ≃ₐ[k] K)

/-- The underlying module of a discrete Galois module is a right exact functor (pinned at the
module universe). -/
local instance (priority := 3000) preservesFiniteColimits_galoisModulesUnderlying' (Λ : Type)
    [Ring Λ] {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K] :
    PreservesFiniteColimits
        (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (K ≃ₐ[k] K)) :=
  Stacks.GroupCohomology.preservesFiniteColimits_continuousModuleToModuleCat.{0, u, u + 1} Λ
      (K ≃ₐ[k] K)

section PointChange

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (g : Y ⟶ X) [ConnectedSpace X.1]
  [ConnectedSpace Y.1] (Λ : Type) [Ring Λ] [Finite Λ] (y₀ : GeometricPoint Y.1)

/-- **Tag 0DV6 with the base point of `X` moved along an equality**: the sheaf on `Y` attached to
the restriction of `ρ` along `π₁(Y, y₀) ⟶ π₁(X, g(y₀)) = π₁(X, x)` is `g⁻¹ ℱ_ρ`. -/
def representationSheafPullbackIsoOfEq {x : GeometricPoint X.1} (h : y₀.map g.hom = x) :
    finiteTypeContinuousModuleRes.{0, u + 1, u + 1} Λ
        ((ContinuousMonoidHom.toContinuousMonoidHom
          (etaleFundamentalGroupContinuousMulEquivOfEq h)).comp
          (etaleFundamentalGroupMap g.hom y₀)) ⋙
        representationSheaf.{u, 0} B Y y₀ Λ ≅
      representationSheaf.{u, 0} B X x Λ ⋙ etaleModuleInverseImage.{u, 0} Λ g.hom := by
  subst h
  exact (representationSheafPullbackIso B g Λ y₀).symm

end PointChange

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (K : Type u) [Field K] [Algebra k K]
  [IsAlgClosure k K] (y : GeometricPoint (fieldBaseChange (Over.mk f) K)) (Λ : Type) [Ring Λ]
  [Finite Λ]

/-- **The sheaf on `X' = X ×_k k'` attached to the restriction of `ρ` is `g⁻¹ ℱ_ρ`** (Tag 0DV6),
naturally in `ρ`, for `g : X' ⟶ X` the projection. -/
def perfectClosureModelRepresentationSheafIso :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f K
    letI := connectedSpace_of_isCurve B (perfectClosureModel B X f K)
      (perfectClosureModelHom B X f K)
    letI := connectedSpace_fieldBaseChange (perfectClosureModelHom B X f K) K
    perfectClosureModelRes B X f K y Λ ⋙
        representationSheaf.{u, 0} B (perfectClosureModel B X f K)
          ((perfectClosureModelPoint B X f K y).map (fieldBaseChangeObjProj B
            (perfectClosureModel B X f K) (perfectClosureModelHom B X f K) K
            (contains_fieldBaseChange_of_isCurve B _ _ K)).hom) Λ ≅
      representationSheaf.{u, 0} B X
          (y.map (fieldBaseChangeObjProj B X f K
            (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ ⋙
        etaleModuleInverseImage.{u, 0} Λ (perfectClosureModelProj B X f K).hom :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f K
  letI := connectedSpace_of_isCurve B (perfectClosureModel B X f K)
    (perfectClosureModelHom B X f K)
  letI := connectedSpace_fieldBaseChange (perfectClosureModelHom B X f K) K
  representationSheafPullbackIsoOfEq B (perfectClosureModelProj B X f K) Λ _
    (perfectClosureModelPoint_map_map B X f K y)

/-- The degree-zero complex of the sheaf attached on `X'` to the restriction of `ρ` is the inverse
image of the degree-zero complex of `ℱ_ρ`. -/
def perfectClosureModelSingleIso
    (M : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f K
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f K
    letI := connectedSpace_of_isCurve B (perfectClosureModel B X f K)
      (perfectClosureModelHom B X f K)
    letI := connectedSpace_fieldBaseChange (perfectClosureModelHom B X f K) K
    (Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
        ((representationSheaf.{u, 0} B (perfectClosureModel B X f K)
          ((perfectClosureModelPoint B X f K y).map (fieldBaseChangeObjProj B
            (perfectClosureModel B X f K) (perfectClosureModelHom B X f K) K
            (contains_fieldBaseChange_of_isCurve B _ _ K)).hom) Λ).obj
          ((perfectClosureModelRes B X f K y Λ).obj M)) ≅
      (etaleModuleInverseImage.{u, 0} Λ
          (pullback.fst f (specAlgebraMap k (perfectClosure k K)))).mapCochainComplexPlus.obj
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf.{u, 0} B X
            (y.map (fieldBaseChangeObjProj B X f K
              (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ).obj M)) :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f K
  letI := connectedSpace_of_isCurve B (perfectClosureModel B X f K)
    (perfectClosureModelHom B X f K)
  letI := connectedSpace_fieldBaseChange (perfectClosureModelHom B X f K) K
  (Stacks.DerivedIndexing.singlePlusFunctor _ 0).mapIso
      ((perfectClosureModelRepresentationSheafIso B X f K y Λ).app M) ≪≫
    (mapCochainComplexPlusSinglePlusIso
      (etaleModuleInverseImage.{u, 0} Λ (perfectClosureModelProj B X f K).hom) _).symm

/-- **The left side of `AlgebraicGeometry.compactSupportDerivedHomologyIsoOfAlgClosure`, forgetting
the Galois action, is `RΓ_c(X_{k̄}, ℱ_ρ)` for the original curve `X` over `k`**: the
Galois-equivariant `RΓ^{Gal}_c(X'_{k̄}, ℱ_{ρ|π₁(X')})` computed on `X' = X ×_k k'`, with its action
forgotten, is `RΓ_c(X_{k̄}, ℱ_ρ) = RΓ(X̄_{k̄}, (j_! ℱ_ρ)|_{X̄_{k̄}})` of Remark 03UI (2), for the
compactification `j : X ⟶ X̄` of `X` over `k`. -/
def perfectClosureCompactSupportForgetIso (j : CompactificationOf (Over.mk f))
    (M : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f K
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f K
    letI := connectedSpace_of_isCurve B (perfectClosureModel B X f K)
      (perfectClosureModelHom B X f K)
    letI := connectedSpace_fieldBaseChange (perfectClosureModelHom B X f K) K
    (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ
        (K ≃ₐ[perfectClosure k K] K)).mapDerivedCategoryPlus.obj
        (galoisDerivedCompactSupport Λ (perfectClosureModelHom B X f K)
          (compactificationFieldBaseChange f j (perfectClosure k K)) K
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            ((representationSheaf.{u, 0} B (perfectClosureModel B X f K)
              ((perfectClosureModelPoint B X f K y).map (fieldBaseChangeObjProj B
                (perfectClosureModel B X f K) (perfectClosureModelHom B X f K) K
                (contains_fieldBaseChange_of_isCurve B _ _ K)).hom) Λ).obj
              ((perfectClosureModelRes B X f K y Λ).obj M)))) ≅
      galoisCompactSupportCohomology.{u, 0} Λ f j K
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf.{u, 0} B X
            (y.map (fieldBaseChangeObjProj B X f K
              (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ).obj M)) :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f K
  letI := connectedSpace_of_isCurve B (perfectClosureModel B X f K)
    (perfectClosureModelHom B X f K)
  letI := connectedSpace_fieldBaseChange (perfectClosureModelHom B X f K) K
  galoisCompactSupportForgetIso Λ (perfectClosureModelHom B X f K)
      (compactificationFieldBaseChange f j (perfectClosure k K)) K _ ≪≫
    (etaleModuleDerivedGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk (compactificationFieldBaseChange f j
          (perfectClosure k K)).toBase) K)).mapIso
      (DerivedCategory.Plus.Q.mapIso
        ((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk (compactificationFieldBaseChange f j
              (perfectClosure k K)).toBase) K)).mapCochainComplexPlus.mapIso
          ((etaleModuleExtensionByZero.{u, 0} Λ
              (compactificationFieldBaseChange f j
                (perfectClosure k K)).immersion).mapCochainComplexPlus.mapIso
            (perfectClosureModelSingleIso B X f K y Λ M)))) ≪≫
    galoisCompactSupportCohomologyFieldExtensionIso Λ f j (perfectClosure k K) K _

/-- **The étale side of `AlgebraicGeometry.geometricGaloisDerivedInvariantsIsoOfAlgClosure`,
forgetting the Galois action, is `RΓ(X_{k̄}, ℱ_ρ|_{X_{k̄}})` for the original curve `X` over
`k`.** -/
def perfectClosureGaloisDerivedSectionsForgetIso
    (M : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f K
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f K
    letI := connectedSpace_of_isCurve B (perfectClosureModel B X f K)
      (perfectClosureModelHom B X f K)
    letI := connectedSpace_fieldBaseChange (perfectClosureModelHom B X f K) K
    (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ
        (K ≃ₐ[perfectClosure k K] K)).mapDerivedCategoryPlus.obj
        ((galoisDerivedGlobalSections Λ (Over.mk (perfectClosureModelHom B X f K)) K).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((representationSheaf.{u, 0} B (perfectClosureModel B X f K)
              ((perfectClosureModelPoint B X f K y).map (fieldBaseChangeObjProj B
                (perfectClosureModel B X f K) (perfectClosureModelHom B X f K) K
                (contains_fieldBaseChange_of_isCurve B _ _ K)).hom) Λ).obj
              ((perfectClosureModelRes B X f K y Λ).obj M)))) ≅
      (etaleModuleDerivedGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) K)).obj
        (fieldBaseChangeRestriction.{u, 0} Λ (Over.mk f) K
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            ((representationSheaf.{u, 0} B X
              (y.map (fieldBaseChangeObjProj B X f K
                (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ).obj M))) :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f K
  letI := connectedSpace_of_isCurve B (perfectClosureModel B X f K)
    (perfectClosureModelHom B X f K)
  letI := connectedSpace_fieldBaseChange (perfectClosureModelHom B X f K) K
  (galoisDerivedGlobalSectionsForgetIso Λ (Over.mk (perfectClosureModelHom B X f K)) K).app _ ≪≫
    (etaleModuleDerivedGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk (perfectClosureModelHom B X f K)) K)).mapIso
      (Functor.mapDerivedCategoryPlusObjSingleIso (etaleModuleInverseImage.{u, 0} Λ
          (fieldBaseChangeProj (Over.mk (perfectClosureModelHom B X f K)) K)) _ ≪≫
        DerivedCategory.Plus.Q.mapIso
          ((mapCochainComplexPlusSinglePlusIso
            (etaleModuleInverseImage.{u, 0} Λ
              (fieldBaseChangeProj (Over.mk (perfectClosureModelHom B X f K)) K)) _).symm ≪≫
          (etaleModuleInverseImage.{u, 0} Λ
              (fieldBaseChangeProj (Over.mk (perfectClosureModelHom B X f K))
                K)).mapCochainComplexPlus.mapIso
            (perfectClosureModelSingleIso B X f K y Λ M))) ≪≫
    fieldBaseChangeExtensionDerivedSectionsIso Λ (Over.mk f) (perfectClosure k K) K _

end AlgebraicGeometry

end

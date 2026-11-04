module

public import StacksFrontier.AlgebraicGeometry.Quot.NumericalEulerLocallyConstant
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPushforwardQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforwardLeftTExact
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedFibreEulerPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationQcqsRestrict
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteUniverses

/-!
# The objects `K_i` of a coherent family are perfect and commute with base change

Let `f : X ⟶ B` be a morphism of algebraic spaces of finite presentation, `E_i` a perfect object
of `D(𝒪_X)`, and `(T, 𝓕)` an object of `Coh_{X/B}`: a scheme `T` over `B` with a finitely
presented `𝒪_{X_T}`-module `𝓕`, flat over `T`, with support proper over `T`.  Stacks 0DNC forms

`K_i = Rf_{T,*}(E_{i,T} ⊗^𝐋 𝓕)`

and cites Stacks 0A1P for two facts about it: `K_i` is a perfect object of `D(𝒪_T)`, and its
formation commutes with base change, that is, for a morphism `(T', 𝓕') ⟶ (T, 𝓕)` of
`Coh_{X/B}` lying over `h : T' ⟶ T`, `K_i(T', 𝓕') ≅ Lh^* K_i(T, 𝓕)`.  This file proves both.
Consequently the function `χ_i(t) = χ(K_i ⊗^𝐋 κ(t))` is compatible with pullback along the
morphisms of `Coh_{X/B}` and locally constant (Stacks 0D1Z), which are the two properties of the
numerical invariants that the substack `Coh^P_{X/B}` of Stacks 0DND is built on.

## Main definitions

* `AlgebraicGeometry.Space.NumericalSituation.numericalDirectImagePullbackIso`: the base change
  isomorphism `K_i(T', 𝓕') ≅ Lh^* K_i(T, 𝓕)` along a morphism of `Coh_{X/B}`.
* `AlgebraicGeometry.Space.NumericalSituation.familyComplex`: the module `𝓕` of an object of
  `Coh_{X/B}` placed in degree `0`, the complex the base change map of Stacks 0A1K is formed on.

## Main results

* `AlgebraicGeometry.Space.NumericalSituation.isPerfect_numericalDirectImage`: `K_i` is perfect.
* `AlgebraicGeometry.Space.NumericalSituation.numericalEuler_eq_of_hom`: `χ_i` is compatible
  with pullback along the morphisms of `Coh_{X/B}`.
* `AlgebraicGeometry.Space.NumericalSituation.isLocallyConstant_numericalEuler`: `χ_i` is locally
  constant.
* `AlgebraicGeometry.Space.NumericalSituation.hasNumericalInvariants_of_hom`: the condition
  `χ_i = P(i)` is inherited along the morphisms of `Coh_{X/B}`.

## Implementation notes

`K_i` is formed with the total right derived functor of the direct image and the derived tensor
product of the small étale ringed site; Stacks 0A1P and 0A1K are proved for the derived direct
image `AlgebraicGeometry.Space.derivedModulePushforward` and the derived tensor bifunctor
`AlgebraicGeometry.Space.smallEtaleDerivedTensor`, and the two direct images are identified by
`AlgebraicGeometry.Space.derivedModulePushforwardIsoTotalRightDerived`.  The module `𝓕` enters
the base change map of Stacks 0A1K as the complex concentrated in degree `0`, whose degreewise
inverse image is the inverse image of `𝓕` placed in degree `0`.

## References

* [Stacks Project, Tag 0DNC](https://stacks.math.columbia.edu/tag/0DNC)
* [Stacks Project, Tag 0A1P](https://stacks.math.columbia.edu/tag/0A1P)
* [Stacks Project, Tag 0A1K](https://stacks.math.columbia.edu/tag/0A1K)
* [Stacks Project, Tag 0D1Z](https://stacks.math.columbia.edu/tag/0D1Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}

namespace NumericalSituation

variable (N : NumericalSituation.{u, v, u} B S hS D)

/-- **Stacks 0A1P, perfectness of `K_i`.**  For an object `(T, 𝓕)` of `Coh_{X/B}` and `i ∈ I`,
the object `K_i = Rf_{T,*}(E_{i,T} ⊗^𝐋 𝓕)` of `D(𝒪_T)` is perfect. -/
theorem isPerfect_numericalDirectImage (A : CoherentObject D) (i : N.I) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (testSpace A).1 (testSpace A).2)
    (smallEtaleRingedSite B S hS (testSpace A).1 (testSpace A).2).IsPerfect
      (N.numericalDirectImage A i) := by
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS (testSpace A).1 (testSpace A).2)
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (testSpace A)))
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS (D.space A.T).1 (D.space A.T).2)
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (D.space A.T)))
  obtain ⟨hp, hU, hprop⟩ := A.properSupport
  have h := isPerfect_derivedModulePushforward_derivedTensor_single (D.projection A.T)
    (D.isFinitePresentation_projection A.T)
    ((smallEtaleDerivedModulePullback B S hS (baseChangeProjection D.f A.T)).obj (N.E i))
    (isPerfect_smallEtaleDerivedModulePullback _ _ (N.perfect i)) A.F
    (SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite' A.F A.finitePresentation)
    A.flat ⟨hU, hprop⟩
  exact isPerfect_of_iso B S hS h
    ((derivedModulePushforwardIsoTotalRightDerived B S hS (D.projection A.T)).app _)

section BaseChange

variable {A' A : CoherentObject D} (φ : CoherentHom A' A)

/-- The morphism `T' ⟶ T` of test spaces underlying a morphism of `Coh_{X/B}`. -/
abbrev testSpaceMap : testSpace A' ⟶ testSpace A :=
  (schemeSpaceFunctor B S hS).map φ.base.left

/-- The square `X_{T'} ⟶ X_T` over `T' ⟶ T` of a morphism of `Coh_{X/B}` is cartesian. -/
theorem isPullback_relativeMap_testSpaceMap :
    IsPullback (D.relativeMap φ.base) (D.projection A'.T) (D.projection A.T) (testSpaceMap φ) :=
  isPullback_baseChangeMap D.f φ.base

/-- The module `𝓕` of an object `(T, 𝓕)` of `Coh_{X/B}`, as the complex concentrated in
degree `0`. -/
abbrev familyComplex (A : CoherentObject D) :
    CochainComplex (Modules.{u, u} B S hS (D.space A.T).1 (D.space A.T).2) ℤ :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj A.F

/-- The terms of `familyComplex A` in nonzero degrees are zero. -/
theorem isZero_familyComplex_X (A : CoherentObject D) {n : ℤ} (hn : n ≠ 0) :
    IsZero ((familyComplex A).X n) :=
  HomologicalComplex.isZero_single_obj_X _ _ _ _ hn

/-- **Stacks 0A1P, base change for `K_i`.**  For a morphism `(T', 𝓕') ⟶ (T, 𝓕)` of
`Coh_{X/B}` lying over `h : T' ⟶ T`, `K_i(T', 𝓕') ≅ Lh^* K_i(T, 𝓕)`.

It is the inverse of the base change map
`Lh^* Rf_{T,*}(E_{i,T} ⊗^𝐋 𝓕[0]) ⟶ Rf_{T',*}(L(h')^* E_{i,T} ⊗^𝐋 (h')^* 𝓕[0])` of Stacks 0A1K,
read through `L(h')^* E_{i,T} ≅ E_{i,T'}` and `(h')^* 𝓕 ≅ 𝓕'`. -/
def numericalDirectImagePullbackIso (i : N.I) :
    N.numericalDirectImage A' i ≅
      (smallEtaleDerivedModulePullback B S hS (testSpaceMap φ)).obj (N.numericalDirectImage A i) :=
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (D.space A.T).1 (D.space A.T).2)
  letI := HasDerivedCategory.standard
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (D.space A.T)))
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (D.space A'.T).1 (D.space A'.T).2)
  letI := HasDerivedCategory.standard
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (D.space A'.T)))
  -- `E_{i,T}` and the base change map of Stacks 0A1K
  let E := (smallEtaleDerivedModulePullback B S hS (baseChangeProjection D.f A.T)).obj (N.E i)
  have hfp := D.isFinitePresentation_projection A.T
  have hiso := isIso_smallEtaleDerivedBaseChangeComp_derivedTensor
    (isPullback_relativeMap_testSpaceMap φ) hfp.2.1 hfp.2.2 E
    (derivedCategoryB_of_isPerfect B S hS _ _
      (isPerfect_smallEtaleDerivedModulePullback _ _ (N.perfect i))) (familyComplex A)
    ⟨0, fun n hn => isZero_familyComplex_X A (by lia)⟩
    (fun n => by
      by_cases hn : n = 0
      · subst hn
        exact SheafOfModules.IsQuasicoherentOnSite.of_iso
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A.F).symm A.quasicoherent
      · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero (isZero_familyComplex_X A hn))
    (fun n => by
      by_cases hn : n = 0
      · subst hn
        exact IsFlatOver.of_iso B S hS _
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A.F).symm A.flat
      · exact isFlatOver_of_isZero B S hS _ (isZero_familyComplex_X A hn))
  -- `K_i` read through the derived direct image of Stacks 0A1K, at `(T, 𝓕)` and at `(T', 𝓕')`
  let e : N.numericalDirectImage A i ≅ (derivedModulePushforward B S hS (D.projection A.T)).obj
      (((smallEtaleDerivedTensor B S hS (D.space A.T)).obj E).obj
        (DerivedCategory.Q.obj (familyComplex A))) :=
    ((derivedModulePushforwardIsoTotalRightDerived B S hS (D.projection A.T)).app _).symm ≪≫
      (derivedModulePushforward B S hS (D.projection A.T)).mapIso
        (((smallEtaleDerivedTensor B S hS (D.space A.T)).obj E).mapIso
          ((DerivedCategory.singleFunctorIsoCompQ _ 0).app A.F))
  let e' : N.numericalDirectImage A' i ≅ (derivedModulePushforward B S hS (D.projection A'.T)).obj
      (((smallEtaleDerivedTensor B S hS (D.space A'.T)).obj
        ((smallEtaleDerivedModulePullback B S hS (baseChangeProjection D.f A'.T)).obj (N.E i))).obj
        (DerivedCategory.Q.obj (familyComplex A'))) :=
    ((derivedModulePushforwardIsoTotalRightDerived B S hS (D.projection A'.T)).app _).symm ≪≫
      (derivedModulePushforward B S hS (D.projection A'.T)).mapIso
        (((smallEtaleDerivedTensor B S hS (D.space A'.T)).obj _).mapIso
          ((DerivedCategory.singleFunctorIsoCompQ _ 0).app A'.F))
  -- `L(h')^* E_{i,T} ≅ E_{i,T'}` and `(h')^* 𝓕[0] ≅ 𝓕'[0]`
  let eE : (smallEtaleDerivedModulePullback B S hS (D.relativeMap φ.base)).obj E ≅
      (smallEtaleDerivedModulePullback B S hS (baseChangeProjection D.f A'.T)).obj (N.E i) :=
    (smallEtaleDerivedModulePullbackCompIso B S hS (D.relativeMap φ.base)
        (baseChangeProjection D.f A.T)).app (N.E i) ≪≫
      (smallEtaleDerivedModulePullbackCongr B S hS
        (baseChangeMap_comp_projection D.f φ.base)).app (N.E i)
  let eF : DerivedCategory.Q.obj
      (((modulePullback B S hS (D.relativeMap φ.base)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (familyComplex A)) ≅ DerivedCategory.Q.obj (familyComplex A') :=
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
          (modulePullback B S hS (D.relativeMap φ.base)) (ComplexShape.up ℤ) 0).app A.F ≪≫
        (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso (asIso φ.fibre))
  e' ≪≫
    (derivedModulePushforward B S hS (D.projection A'.T)).mapIso
      ((((smallEtaleDerivedTensor B S hS (D.space A'.T)).mapIso eE).app _).symm ≪≫
        ((smallEtaleDerivedTensor B S hS (D.space A'.T)).obj _).mapIso eF.symm) ≪≫
    (@asIso _ _ _ _ _ hiso).symm ≪≫
    (smallEtaleDerivedModulePullback B S hS (testSpaceMap φ)).mapIso e.symm

/-- **The functions `χ_i` are compatible with pullback along the morphisms of `Coh_{X/B}`.**  For
a morphism `(T', 𝓕') ⟶ (T, 𝓕)` over `h : T' ⟶ T` and a point `t'` of `T'`,
`χ_i(T', 𝓕')(t') = χ_i(T, 𝓕)(h(t'))`: by Stacks 0A1P, `K_i(T', 𝓕') ≅ Lh^* K_i(T, 𝓕)`, and the
derived fibre of `Lh^* K` at `t'` is that of `K` at `h(t')`. -/
theorem numericalEuler_eq_of_hom (i : N.I) (t : points B S hS (yoneda.obj A'.T.left)) :
    N.numericalEuler A' i t =
      N.numericalEuler A i (pointsMap B S hS _ (yoneda.map φ.base.left) t) :=
  (congrFun (derivedFibreEuler_congr _ (N.numericalDirectImagePullbackIso φ i)) t).trans
    (derivedFibreEuler_derivedPullback_of_isPerfect (testSpaceMap φ) _
      (N.isPerfect_numericalDirectImage A i) t)

include φ in
/-- **`Coh^P_{X/B}` is inherited along the morphisms of `Coh_{X/B}`**: if `(T, 𝓕)` has the
numerical invariants `P`, so has every object mapping to it. -/
theorem hasNumericalInvariants_of_hom (h : N.HasNumericalInvariants A) :
    N.HasNumericalInvariants A' :=
  fun i t => (N.numericalEuler_eq_of_hom φ i t).trans (h i _)

end BaseChange

/-- **The functions `χ_i` are locally constant** (Stacks 0D1Z applied to the perfect objects
`K_i` of Stacks 0A1P). -/
theorem isLocallyConstant_numericalEuler (A : CoherentObject D) (i : N.I) :
    IsLocallyConstant (N.numericalEuler A i) :=
  N.isLocallyConstant_numericalEuler_of_isPerfect A i (N.isPerfect_numericalDirectImage A i)

end NumericalSituation

end AlgebraicGeometry.Space

end

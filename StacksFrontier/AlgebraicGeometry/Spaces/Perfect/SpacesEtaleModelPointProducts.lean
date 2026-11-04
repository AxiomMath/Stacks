module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleLimitComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.QcqsPerfectGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelToPointFlat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.UnboundedEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.ProjectionFormulaDualHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.StructureSheafPerfect
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.MapOutOfALocallyConstantComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.TermFunctorExactness

/-!
# Maps out of a perfect object into `𝒪_X ⊗_R M` commute with countable products

Let `f : X ⟶ T` be a flat morphism from a quasi-compact and quasi-separated algebraic space to an
affine `T`, with `R = Γ(T, 𝒪_T)`, and let `P` be a perfect object of `D(𝒪_X)`. The proof of
Stacks 0D3F computes `Hom(P, (𝒪_X ⊗_R M)[0])` as `H⁰(RΓ(X, P^∨) ⊗^L_R M)` (Stacks 08JJ, 08IN) and,
`RΓ(X, P^∨)` being perfect (Stacks 0CTM), as `Hom(RΓ(X, P^∨)^∨, M[0])`. This file carries out that
computation on the spaces-étale model, where `RΓ(X, -)` is the derived direct image along the
morphism `X ⟶ (pt, R)` of ringed topoi:

* `Lf^*(M[0]) = (𝒪_X ⊗_R M)[0]` naturally in `M` (`singleBaseRingTensorModuleIso`), `Lf^*` being
  degreewise for flat `f`;
* `Hom(P, Lf^*K) ≅ Hom(L^∨, K)` for `L = Rf_*P^∨` perfect
  (`Stacks.Cohomology.ProjectionFormulaDualHom.derivedPullbackCoyonedaIso`), the projection formula
  of Stacks 0B56 being invertible at `P^∨` by Stacks 08IN at the point;
* placing an `R`-module in degree zero commutes with countable products (Stacks 07KC).

So `M ↦ Hom(P, (𝒪_X ⊗_R M)[0])` commutes with countable products, which is the product property
consumed by `AlgebraicGeometry.Space.bijective_comp_single_limitComparison_baseRingTensorModule`.

## Main results

* `AlgebraicGeometry.Space.coyonedaSingleBaseRingTensorModuleIso`:
  `Hom(P, (𝒪_X ⊗_R M)[0]) ≅ Hom(L^∨, M[0])`, naturally in `M`.
* `AlgebraicGeometry.Space.bijective_comp_single_pi_baseRingTensorModule`: the product property.
* `bijective_comp_single_limitComparison_baseRingTensorModule_of_isPerfect_derivedPushforward`:
  Stacks 0D3F for `f` flat and of finite presentation, once `RΓ(X, -)` on the spaces-étale model
  preserves perfect objects.
* `AlgebraicGeometry.Space.isPerfect_point_of_isPerfect_pointDerivedEquiv`: a perfect complex of
  `R`-modules is perfect over the punctual ringed topos.

## References

* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
* [Stacks Project, Tag 08IN](https://stacks.math.columbia.edu/tag/08IN)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 0B56](https://stacks.math.columbia.edu/tag/0B56)
* [Stacks Project, Tag 07KC](https://stacks.math.columbia.edu/tag/07KC)
* [Stacks Project, Tag 09IY](https://stacks.math.columbia.edu/tag/09IY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard
attribute [-instance] SheafOfModules.hasColimitsOfShape_discrete_derivedCategory

section Point

variable {R : Type u} [CommRing R]

/-- **Placing a module over the punctual ringed topos in degree zero commutes with countable
products.** Products of modules over the point are exact, being those of `R`-modules, so the
localization `Q` preserves them (Stacks 07KC), and so does placing a module in degree zero. -/
theorem preservesLimitsOfShape_singleFunctor_point :
    PreservesLimitsOfShape (Discrete ℕ)
      (DerivedCategory.singleFunctor (pointRingedTopos (CommRingCat.of R)).Modules 0) := by
  have : HasExactLimitsOfShape (Discrete ℕ) (pointRingedTopos (CommRingCat.of R)).Modules :=
    HasExactLimitsOfShape.of_codomain_equivalence (Discrete ℕ)
      (baseRingPointModulesEquiv (R := R)).symm
  have := Stacks.DerivedProducts.preservesLimitsOfShape_Q
    (A := (pointRingedTopos (CommRingCat.of R)).Modules) (I := ℕ)
  have : PreservesLimitsOfShape (Discrete ℕ)
      (CochainComplex.singleFunctor (pointRingedTopos (CommRingCat.of R)).Modules 0) :=
    inferInstanceAs (PreservesLimitsOfShape (Discrete ℕ)
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0))
  have : PreservesLimitsOfShape (Discrete ℕ)
      (CochainComplex.singleFunctor (pointRingedTopos (CommRingCat.of R)).Modules 0 ⋙
        DerivedCategory.Q) := comp_preservesLimitsOfShape _ _
  exact preservesLimitsOfShape_of_natIso (DerivedCategory.singleFunctorIsoCompQ _ 0).symm

/-- **A perfect complex of `R`-modules gives a perfect object over the punctual ringed topos.** If
the image of `K` in `D(R)` is isomorphic to a bounded complex of finite projective `R`-modules,
then `K` is perfect (Stacks 08G5): that complex, carried to the point, is strictly perfect. -/
theorem isPerfect_point_of_isPerfect_pointDerivedEquiv
    (K : DerivedCategory (pointRingedTopos (CommRingCat.of R)).Modules)
    (hK : StacksDraft.Perfect.IsPerfect ((pointDerivedEquiv (R := R)).functor.obj K)) :
    (pointRingedTopos (CommRingCat.of R)).toRingedSite.IsPerfect K := by
  obtain ⟨P, a, b, ha, hb, hfin, hproj, ⟨i⟩⟩ := hK
  let e := baseRingPointModulesEquiv (R := R)
  have hbd : {n : ℤ | ¬ IsZero (P.X n)}.Finite := by
    refine (Set.finite_Icc a b).subset fun n hn => ⟨?_, ?_⟩
    · by_contra h
      exact hn (P.isZero_of_isStrictlyGE a n (by omega))
    · by_contra h
      exact hn (P.isZero_of_isStrictlyLE b n (by omega))
  have hunit : e.inverse.obj (ModuleCat.of R R) ≅ SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (pointRingedTopos (CommRingCat.of R)).O) :=
    e.inverse.mapIso ((show ModuleCat.of R (Shrink.{u} R) ≅ ModuleCat.of R R from
        (Shrink.linearEquiv R R).toModuleIso).symm ≪≫
        baseRingPointModulesEquivUnitIso.symm) ≪≫ e.unitIso.symm.app _
  obtain ⟨L, hL, ⟨j⟩⟩ := RingedSite.isPerfect_Q_obj_of_isStrictlyPerfect
    (pointRingedTopos (CommRingCat.of R)).toRingedSite _
    (Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex_of_finite_projective
      e.inverse hunit hbd hfin hproj)
  exact ⟨L, hL, ⟨j ≪≫ (e.inverse.mapDerivedCategoryFactors.app P).symm ≪≫
    e.inverse.mapDerivedCategory.mapIso i.symm ≪≫
      ((pointDerivedEquiv (R := R)).unitIso.app K).symm⟩⟩

end Point

section Products

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}

/-- **`𝒪_X ⊗_R M` placed in degree zero is `Lf^*` of `M` placed in degree zero, naturally in `M`**,
for flat `f : X ⟶ T` over an affine `T` and the morphism `X ⟶ (pt, Γ(T, 𝒪_T))`. -/
def singleBaseRingTensorModuleIso (f : X ⟶ schemeSpace T)
    (hflat : IsFlat B S hS f.hom) (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) :
    letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f hflat hT
    (baseRingPointModulesEquiv (R := baseRing B S hS T)).inverse ⋙
        DerivedCategory.singleFunctor _ 0 ⋙
        derivedPullback (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)) ⋙
        (spacesEtaleModelModulesEquiv B S hS X).functor.mapDerivedCategory ≅
      baseRingTensorModule B S hS X (baseRingHomOfMap f) ⋙ DerivedCategory.singleFunctor _ 0 :=
  letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f hflat hT
  letI := preservesFiniteLimits_pullbackTopos_toBaseRing f hflat hT
  letI := preservesFiniteColimits_pullbackTopos_toBaseRing (B := B) (S := S) (hS := hS) (X := X)
    (baseRingHomOfMap f)
  let f' := spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)
  let E := spacesEtaleModelModulesEquiv B S hS X
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (Stacks.Cohomology.CohomologicalDescent.derivedPullbackNatIso f') _)) ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (f'.pullbackTopos.mapDerivedCategorySingleFunctor 0) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (E.functor.mapDerivedCategorySingleFunctor 0) ≪≫
      (Functor.associator _ _ _).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (pullbackToBaseRingIso B S hS X (baseRingHomOfMap f)) _

/-- The derived equivalence `D(𝒪_X) ≌ D(spaces-étale model)`, with functor the derived functor of
the inverse of `AlgebraicGeometry.Space.spacesEtaleModelModulesEquiv`. -/
def spacesEtaleModelDerivedEquivSymm (X : AlgebraicSpaces B S hS) :
    DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ≌
      DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules :=
  Stacks.DerivedGlueing.mapDerivedCategoryEquivalence
    (spacesEtaleModelModulesEquiv B S hS X).inverse
    (spacesEtaleModelModulesEquiv B S hS X).functor
    (spacesEtaleModelModulesEquiv B S hS X).counitIso.symm
    (spacesEtaleModelModulesEquiv B S hS X).unitIso.symm

attribute [local instance] hasCoproducts_derivedCategory_point
  hasCoproducts_derivedCategory_spacesEtaleModel

/-- **Maps out of a perfect object into `(𝒪_X ⊗_R M)[0]` are maps out of a perfect complex of
`R`-modules into `M[0]`, naturally in `M`.** Let `f : X ⟶ T` be flat with `T` affine and `X`
quasi-compact and quasi-separated, let `P` be perfect in `D(𝒪_X)`, let `P'` be its image on the
spaces-étale model, and suppose that `L = RΓ(X, P'^∨)` is perfect on the point. Then
`Hom(P, (𝒪_X ⊗_R M)[0]) ≅ Hom(L^∨, M[0])`, naturally in the `R`-module `M`. -/
def coyonedaSingleBaseRingTensorModuleIso (hZ : B.Contains (⊤_ Scheme.{u}))
    (f : X ⟶ schemeSpace T) (hflat : IsFlat B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (P : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hP : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect P)
    (hL : letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f hflat hT
      (pointRingedTopos (CommRingCat.of (baseRing B S hS T))).toRingedSite.IsPerfect
      ((derivedPushforward (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).obj
        (RingedSite.derivedDual (spacesEtaleModelRingedTopos B S hS X).toRingedSite
          ((spacesEtaleModelModulesEquiv B S hS X).inverse.mapDerivedCategory.obj P)))) :
    letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f hflat hT
    baseRingTensorModule B S hS X (baseRingHomOfMap f) ⋙ DerivedCategory.singleFunctor _ 0 ⋙
        coyoneda.obj (op P) ≅
      (baseRingPointModulesEquiv (R := baseRing B S hS T)).inverse ⋙
        DerivedCategory.singleFunctor _ 0 ⋙
        coyoneda.obj (op (RingedSite.derivedDual
          (pointRingedTopos (CommRingCat.of (baseRing B S hS T))).toRingedSite
          ((derivedPushforward (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).obj
            (RingedSite.derivedDual (spacesEtaleModelRingedTopos B S hS X).toRingedSite
              ((spacesEtaleModelModulesEquiv B S hS X).inverse.mapDerivedCategory.obj P))))) :=
  letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f hflat hT
  let f' := spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)
  let hmos := isMorphismOfSites_spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)
  let D := spacesEtaleModelDerivedEquivSymm X
  let P' := (spacesEtaleModelModulesEquiv B S hS X).inverse.mapDerivedCategory.obj P
  have hP' : (spacesEtaleModelRingedTopos B S hS X).toRingedSite.IsPerfect P' :=
    isPerfect_spacesEtaleModelModulesEquiv_inverse B S hS X P hP
  have hpf : ∀ K, IsIso
      (Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.projectionFormulaMap f' hmos
        (RingedSite.derivedDual (spacesEtaleModelRingedTopos B S hS X).toRingedSite P') K) :=
    fun K => isIso_projectionFormulaMap_spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)
      hZ hXqc hXqs _
      (derivedCategoryB_isQuasicoherentOnSite_of_isPerfect_of_isAlgebraicSpace B S hS X.1 X.2 _
        (isPerfect_spacesEtaleModelModulesEquiv_functor B S hS X _
          (RingedSite.isPerfect_derivedDual _ _ hP'))) K
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (singleBaseRingTensorModuleIso f hflat hT).symm
      (coyoneda.obj (op P)) ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (D.toAdjunction.compCoyonedaIso.app (op P)).symm ≪≫
        Stacks.Cohomology.ProjectionFormulaDualHom.derivedPullbackCoyonedaIso f' hmos P' hP'
          hpf hL))

/-- **Maps out of a perfect object into `(𝒪_X ⊗_R ∏ M_n)[0]` are families of maps into the
`(𝒪_X ⊗_R M_n)[0]`.** Under the hypotheses of
`AlgebraicGeometry.Space.coyonedaSingleBaseRingTensorModuleIso`, the map
`Hom(P, (𝒪_X ⊗_R ∏ M_n)[0]) ⟶ ∏ Hom(P, (𝒪_X ⊗_R M_n)[0])` induced by the projections is
bijective: by that isomorphism it is the corresponding map for `Hom(L^∨, -[0])` on `D(R)`, and
placing a module in degree zero commutes with countable products. -/
theorem bijective_comp_single_pi_baseRingTensorModule (hZ : B.Contains (⊤_ Scheme.{u}))
    (f : X ⟶ schemeSpace T) (hflat : IsFlat B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (P : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hP : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect P)
    (hL : letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f hflat hT
      (pointRingedTopos (CommRingCat.of (baseRing B S hS T))).toRingedSite.IsPerfect
      ((derivedPushforward (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).obj
        (RingedSite.derivedDual (spacesEtaleModelRingedTopos B S hS X).toRingedSite
          ((spacesEtaleModelModulesEquiv B S hS X).inverse.mapDerivedCategory.obj P))))
    (M : ℕ → ModuleCat.{u} (baseRing B S hS T)) :
    Function.Bijective
      (fun a : P ⟶ (DerivedCategory.singleFunctor _ 0).obj
          ((baseRingTensorModule B S hS X (baseRingHomOfMap f)).obj (∏ᶜ M)) =>
        fun n : ℕ => a ≫ (DerivedCategory.singleFunctor _ 0).map
          ((baseRingTensorModule B S hS X (baseRingHomOfMap f)).map (Pi.π M n))) := by
  let H := baseRingTensorModule B S hS X (baseRingHomOfMap f) ⋙
    DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0 ⋙ coyoneda.obj (op P)
  have : PreservesLimitsOfShape (Discrete ℕ)
      (DerivedCategory.singleFunctor
        (pointRingedTopos (CommRingCat.of (baseRing B S hS T))).Modules 0) :=
    preservesLimitsOfShape_singleFunctor_point
  have : PreservesLimitsOfShape (Discrete ℕ) H :=
    preservesLimitsOfShape_of_natIso
      (coyonedaSingleBaseRingTensorModuleIso hZ f hflat hT hXqc hXqs P hP hL).symm
  let hlim := isLimitOfPreserves H (limit.isLimit (Discrete.functor M))
  let e := Types.isLimitEquivSections hlim
  have he : ∀ (a : H.obj (∏ᶜ M)) (n : ℕ),
      (e a).val ⟨n⟩ = a ≫ (DerivedCategory.singleFunctor _ 0).map
        ((baseRingTensorModule B S hS X (baseRingHomOfMap f)).map (Pi.π M n)) := fun a n =>
    Types.isLimitEquivSections_apply hlim ⟨n⟩ a
  refine ⟨fun a b hab => e.injective (Subtype.ext (funext fun j => ?_)), fun g => ?_⟩
  · obtain ⟨n⟩ := j
    rw [he, he]
    exact congrFun hab n
  · let s : (Discrete.functor M ⋙ H).sections := ⟨fun j => g j.as, fun {j j'} φ => by
      obtain rfl : j = j' := Discrete.ext (Discrete.eq_of_hom φ)
      rw [Subsingleton.elim φ (𝟙 j), CategoryTheory.Functor.map_id]
      rfl⟩
    exact ⟨e.symm s, funext fun n =>
      (he (e.symm s) n).symm.trans (by rw [Equiv.apply_symm_apply])⟩

/-- **Stacks 0D3F from perfectness of `RΓ` on the spaces-étale model.** Let `f : X ⟶ T` be flat
and of finite presentation over an affine `T`, with `R = Γ(T, 𝒪_T)`, and let `(M_n)` be an inverse
system of `R`-modules with surjective transition maps. Suppose that `RΓ(X, -)`, read as the derived
direct image along `X ⟶ (pt, R)` on the spaces-étale model, carries perfect objects to perfect
objects. Then composition with the canonical map `𝒪_X ⊗_R lim M_n ⟶ lim 𝒪_X ⊗_R M_n`, placed in
degree zero, is bijective on maps out of every object of `D_QCoh(𝒪_X)`.

The generator is the perfect generator of Stacks 09IY; its product property is
`AlgebraicGeometry.Space.bijective_comp_single_pi_baseRingTensorModule`. -/
theorem bijective_comp_single_limitComparison_baseRingTensorModule_of_isPerfect_derivedPushforward
    (hZ : B.Contains (⊤_ Scheme.{u})) (f : X ⟶ schemeSpace T) (hflat : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (Msys : ℕᵒᵖ ⥤ ModuleCat.{u} (baseRing B S hS T))
    (hsurj : ∀ n : ℕ, Function.Surjective (Msys.map (homOfLE (Nat.le_succ n)).op))
    [HasProduct fun n : ℕ =>
      (baseRingTensorModule B S hS X (baseRingHomOfMap f)).obj (Msys.obj ⟨n⟩)]
    [HasLimit (Msys ⋙ baseRingTensorModule B S hS X (baseRingHomOfMap f))]
    (hpush : ∀ K, (spacesEtaleModelRingedTopos B S hS X).toRingedSite.IsPerfect K →
      (pointRingedTopos (CommRingCat.of (baseRing B S hS T))).toRingedSite.IsPerfect
        ((derivedPushforward (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).obj K))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hE : qcohDerivedProp B S hS X E) :
    Function.Bijective
      (fun a : E ⟶ (DerivedCategory.singleFunctor _ 0).obj
          ((baseRingTensorModule B S hS X (baseRingHomOfMap f)).obj (limit Msys)) =>
        a ≫ (DerivedCategory.singleFunctor _ 0).map
          (limit.post Msys (baseRingTensorModule B S hS X (baseRingHomOfMap f)))) := by
  obtain ⟨hqc, hqs⟩ := qcqs_of_isFinitePresentation_schemeSpace hZ f hT hfp
  obtain ⟨P, hP, hgen⟩ := exists_isPerfect_isZero_iff_forall_hom_shift_eq_zero B S hS hZ X hqc hqs
  let G : (qcohDerivedProp B S hS X).FullSubcategory :=
    ⟨P, derivedCategoryB_isQuasicoherentOnSite_of_isPerfect_of_isAlgebraicSpace B S hS X.1 X.2 P hP⟩
  have hG : (ObjectProperty.singleton G).IsWeakTriangulatedGenerator := by
    intro K hK
    refine IsZero.of_full_of_faithful_of_isZero (qcohDerivedProp B S hS X).ι K
      ((hgen K.obj K.property).2 fun n g => ?_)
    let c := ((qcohDerivedProp B S hS X).ι.commShiftIso n).app G
    have hg' := hK ((qcohDerivedProp B S hS X).ι.preimage (c.hom ≫ g))
      ⟨G, n, Iso.refl _, (ObjectProperty.singleton_iff G G).2 rfl⟩
    have : g = c.inv ≫ (qcohDerivedProp B S hS X).ι.map
        ((qcohDerivedProp B S hS X).ι.preimage (c.hom ≫ g)) := by
      rw [Functor.map_preimage, Iso.inv_hom_id_assoc]
    rw [this, hg', Functor.map_zero, comp_zero]
  refine bijective_comp_single_limitComparison_baseRingTensorModule_of_isFinitePresentation hZ f
    hflat hfp hT Msys hsurj G hG (fun k => ?_) E hE
  exact bijective_comp_single_pi_baseRingTensorModule hZ f hflat hT hqc hqs (P⟦k⟧)
    (RingedSite.isPerfect_shift_general_of_hasDerivedCategory _ P hP k)
    (hpush _ (RingedSite.isPerfect_derivedDual _ _
      (isPerfect_spacesEtaleModelModulesEquiv_inverse B S hS X _
        (RingedSite.isPerfect_shift_general_of_hasDerivedCategory _ P hP k))))
    (fun n => Msys.obj ⟨n⟩)

end Products

end AlgebraicGeometry.Space

end

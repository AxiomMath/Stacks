module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FrobeniusTwistArrows
public import StacksFrontier.Homology.DerivedCategory.PlusModelTransport

/-!
# Arrow 1 of the proof of [Stacks, Tag 07N5] at two models of the derived categories

The base change map (60.26.4.1) of the proof of [Stacks, Tag 07N5],

`RΓ(Cris(X/S), E) ⊗^L_{A, σ} A ⟶ RΓ(Cris(X^{(1)}/S), E^{(1)})`,

is `...SmallSite.baseChangeArrow07QC T E`.  It is built from *choices* of derived categories
(`CategoryTheory.HasDerivedCategory` instances) of the sheaves of modules on the small and the big
crystalline sites of `X/S` and of `X^{(1)}/S`, and of `A`-modules, `A = Γ(S, 𝒪_S)`.  This file
proves that whether it is an isomorphism does not depend on those choices, so that a statement
about it may be made at whatever models a consumer has in scope and proved at any convenient
ones, for instance `CategoryTheory.HasDerivedCategory.standard`.

## How the comparison goes

* Arrow 1 is the transpose across `- ⊗^L_{A, σ} A ⊣ σ_*` of a `σ`-semilinear map `g`, and a
  transpose is invertible exactly when `g` is a universal arrow into `σ_*`
  (`StacksDraft.DerivedModel.PlusTransport.isIso_homEquiv_symm_iff`).  The derived tensor product
  disappears from the question.
* `g` is the big-site comparison `...SmallSite.derivedChangeBaseBigGlobalSectionsTrans` at `E[0]`
  up to isomorphisms of its source and its target (the passages from the big to the small sites,
  and `R u^*(E[0]) ≅ (u^* E)[0]`), and being a universal arrow is invariant under those
  (`isIso_baseChangeArrow07QC_iff_bijective`).  The models of the small sites disappear.
* `...SmallSite.derivedChangeBaseBigGlobalSectionsTrans` is assembled from four constructions on
  right derived functors, each of which is compatible with the comparison of two models
  (`StacksFrontier/Homology/DerivedCategory/PlusModelTransport.lean`); so it is
  (`derivedChangeBaseBigGlobalSectionsTrans_compat`), and a universal arrow at one model is one at
  the other (`bijective_derivedChangeBaseBigGlobalSectionsTrans_iff`).

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `isIso_baseChangeArrow07QC_iff_of_models` — **arrow 1 is an isomorphism at one choice of the
  five models exactly when it is one at any other**, in arbitrary universes.
* `isIso_baseChangeArrow07QC_iff_standard` — the same against the standard models.
* `isIso_baseChangeArrow07QC_iff_bijective` — arrow 1 is an isomorphism exactly when the big-site
  comparison at `E[0]` is a universal arrow into `σ_*`.

## What is and is not proved

Nothing here asserts that arrow 1 is an isomorphism; that is
`...SmallSite.isIso_baseChangeArrow07QC_of_inputs` and its relatives.  No `@[stacks]` attribute is
placed in this file: its statements compare two Lean choices of the same mathematical object.

## References

* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open StacksDraft.DerivedModel.PlusTransport
open scoped AlgebraicGeometry

universe u wS wB wA zS zB zA

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **`RΓ(CRIS(X/S), -)` read at two models**: `rightDerivedIso` for the global sections functor
of the big crystalline site, stated with `derivedBigModuleGlobalSectionsFunctor`. -/
def derivedBigModuleGlobalSectionsIso (S : GlobalCrystallineSituation.{u})
    (hB : HasDerivedCategory.{wB} (BigModuleSheaf S))
    (hA : HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)))
    (kB : HasDerivedCategory.{zB} (BigModuleSheaf S))
    (kA : HasDerivedCategory.{zA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))) :
    @derivedBigModuleGlobalSectionsFunctor S hB hA ⋙ plusFunctor hA kA ≅
      plusFunctor hB kB ⋙ @derivedBigModuleGlobalSectionsFunctor S kB kA :=
  rightDerivedIso hB kB hA kA (bigBaseModuleGlobalSections S)

section ChangeBase

variable {S S' : GlobalCrystallineSituation.{u}}
  (hB : HasDerivedCategory.{wB} (BigModuleSheaf S))
  (hB' : HasDerivedCategory.{wB} (BigModuleSheaf S'))
  (hA : HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)))
  (hA' : HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤)))
  (kB : HasDerivedCategory.{zB} (BigModuleSheaf S))
  (kB' : HasDerivedCategory.{zB} (BigModuleSheaf S'))
  (kA : HasDerivedCategory.{zA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)))
  (kA' : HasDerivedCategory.{zA} (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤)))
  (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
  (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)

/-- **The target of `derivedChangeBaseBigGlobalSectionsTrans` read at two models**: the
comparison `R u^* ⋙ RΓ(CRIS(X/S), -) ⋙ res_*` at the first models, followed by the comparison
of `D⁺(Mod_{A'})`, is the comparison of `D⁺(Mod_{𝒪_{Y/S'}})` followed by the same functor at the
second models. -/
def derivedChangeBaseBigGlobalSectionsTransTargetIso :
    (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hB' hB (changeBaseBigModulePullback S S' f g h)
        _ _ ⋙ @derivedBigModuleGlobalSectionsFunctor S hB hA ⋙
          @Functor.mapDerivedCategoryPlus _ _ _ hA _ _ _ hA'
            (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f)) _ _ _) ⋙
        plusFunctor hA' kA' ≅
      plusFunctor hB' kB' ⋙
        (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ kB' kB
          (changeBaseBigModulePullback S S' f g h) _ _ ⋙
          @derivedBigModuleGlobalSectionsFunctor S kB kA ⋙
            @Functor.mapDerivedCategoryPlus _ _ _ kA _ _ _ kA'
              (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f)) _ _ _) :=
  transportComp (rightDerivedIso hB' kB' hB kB (changeBaseBigModulePullback S S' f g h))
    (transportComp (derivedBigModuleGlobalSectionsIso S hB hA kB kA)
      (mapDerivedCategoryPlusIso hA kA hA' kA'
        (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f))))

/-- **`derivedChangeBaseBigGlobalSectionsTrans` does not depend on the models**: it is
compatible with the comparisons of the models of the derived categories. -/
theorem derivedChangeBaseBigGlobalSectionsTrans_compat :
    Functor.whiskerRight (@derivedChangeBaseBigGlobalSectionsTrans S S' hB hB' hA hA' f g h)
        (plusFunctor hA' kA') ≫
      (derivedChangeBaseBigGlobalSectionsTransTargetIso hB hB' hA hA' kB kB' kA kA' f g h).hom =
    (derivedBigModuleGlobalSectionsIso S' hB' hA' kB' kA').hom ≫
      Functor.whiskerLeft (plusFunctor hB' kB')
        (@derivedChangeBaseBigGlobalSectionsTrans S S' kB kB' kA kA' f g h) :=
  compat_comp
    (rightDerivedFunctorPlusNatTrans_compat hB' kB' hA' kA'
      (changeBaseBigBaseGlobalSectionsTrans f g h))
    (compat_comp
      (rightDerivedPlusCompTrans_compat hB' kB' hB kB hA' kA'
        (changeBaseBigModulePullback S S' f g h)
        (bigBaseModuleGlobalSections S ⋙
          ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f)))
      (compat_whiskerLeft _
        (compat_comp
          (rightDerivedFunctorPlusComp_compat hB kB hA kA hA' kA'
            (bigBaseModuleGlobalSections S)
            (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f)))
          (compat_whiskerLeft _
            (rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_compat hA kA hA' kA'
              (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f)))))))

/-- **The universal property of the big-site comparison does not depend on the models.** The
comparison `derivedChangeBaseBigGlobalSectionsTrans f g h` at `N[0]` is a universal arrow into
restriction of scalars along `baseChangeRingHom f` at the models `hB, hB', hA, hA'` exactly when
it is one at the models `kB, kB', kA, kA'`. -/
theorem bijective_derivedChangeBaseBigGlobalSectionsTrans_iff (N : BigModuleSheaf S') :
    (∀ Z, Function.Bijective
      (fun φ : (@DerivedCategory.Plus.ι _ _ _ hA).obj
          ((@derivedBigModuleGlobalSectionsFunctor S hB hA).obj
            ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hB' hB
                (changeBaseBigModulePullback S S' f g h) _ _).obj
              ((@DerivedCategory.Plus.singleFunctor _ _ _ hB' 0).obj N))) ⟶ Z =>
        (@DerivedCategory.Plus.ι _ _ _ hA').map
          ((@derivedChangeBaseBigGlobalSectionsTrans S S' hB hB' hA hA' f g h).app
            ((@DerivedCategory.Plus.singleFunctor _ _ _ hB' 0).obj N)) ≫
          (@Functor.mapDerivedCategory _ _ _ hA _ _ _ hA'
            (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f)) _ _ _).map φ)) ↔
    (∀ Z, Function.Bijective
      (fun φ : (@DerivedCategory.Plus.ι _ _ _ kA).obj
          ((@derivedBigModuleGlobalSectionsFunctor S kB kA).obj
            ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ kB' kB
                (changeBaseBigModulePullback S S' f g h) _ _).obj
              ((@DerivedCategory.Plus.singleFunctor _ _ _ kB' 0).obj N))) ⟶ Z =>
        (@DerivedCategory.Plus.ι _ _ _ kA').map
          ((@derivedChangeBaseBigGlobalSectionsTrans S S' kB kB' kA kA' f g h).app
            ((@DerivedCategory.Plus.singleFunctor _ _ _ kB' 0).obj N)) ≫
          (@Functor.mapDerivedCategory _ _ _ kA _ _ _ kA'
            (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f)) _ _ _).map φ)) := by
  let U := changeBaseBigModulePullback S S' f g h
  let res := ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f)
  let Y := (@DerivedCategory.Plus.singleFunctor _ _ _ hB' 0).obj N
  let σ := plusSingleObjIso hB' kB' 0 N
  let ΦΓ := derivedBigModuleGlobalSectionsIso S' hB' hA' kB' kA'
  let ΦΓ' := derivedBigModuleGlobalSectionsIso S hB hA kB kA
  let ΦU := rightDerivedIso hB' kB' hB kB U
  let Trans₁ := @derivedChangeBaseBigGlobalSectionsTrans S S' hB hB' hA hA' f g h
  let Trans₂ := @derivedChangeBaseBigGlobalSectionsTrans S S' kB kB' kA kA' f g h
  let a' := ΦΓ.app Y ≪≫ (@derivedBigModuleGlobalSectionsFunctor S' kB' kA').mapIso σ
  let a := (@DerivedCategory.Plus.ι _ _ _ kA').mapIso a'
  let b' := ΦΓ'.app ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hB' hB U _ _).obj Y) ≪≫
    (@derivedBigModuleGlobalSectionsFunctor S kB kA).mapIso
      (ΦU.app Y ≪≫ (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ kB' kB U _ _).mapIso σ)
  let b := (@DerivedCategory.Plus.ι _ _ _ kA).mapIso b'
  have hc := NatTrans.congr_app
    (derivedChangeBaseBigGlobalSectionsTrans_compat hB hB' hA hA' kB kB' kA kA' f g h) Y
  have hn := Trans₂.naturality σ.hom
  refine bijective_comp_map_iff_of_iso (fullFunctor hA kA) (fullFunctor hA' kA')
    (mapDerivedCategoryIso hA kA hA' kA' res) _ _ a b ?_
  have P : (plusFunctor hA' kA').map (Trans₁.app Y) ≫
      (mapDerivedCategoryPlusIso hA kA hA' kA' res).hom.app
          ((@derivedBigModuleGlobalSectionsFunctor S hB hA).obj
              ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hB' hB U _ _).obj Y)) ≫
      (@Functor.mapDerivedCategoryPlus _ _ _ kA _ _ _ kA' res _ _ _).map b'.hom =
      a'.hom ≫ Trans₂.app ((@DerivedCategory.Plus.singleFunctor _ _ _ kB' 0).obj N) := by
    simp only [derivedChangeBaseBigGlobalSectionsTransTargetIso, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, transportComp_hom_app,
      Functor.comp_map, Category.assoc] at hc
    simp only [a', b', Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp,
      Category.assoc]
    rw [reassoc_of% hc]
    simp only [Functor.comp_map] at hn
    rw [hn]
  exact congrArg (@DerivedCategory.Plus.ι _ _ _ kA').map P

end ChangeBase

section Twist

variable (T : Crystalline.FCrystalSituation.{u})

section OneModel

variable [HasDerivedCategory.{wS} (ModuleSheaf T.global)]
  [HasDerivedCategory.{wS} (ModuleSheaf T.frobeniusTwistSituation)]
  [HasDerivedCategory.{wB} (BigModuleSheaf T.global)]
  [HasDerivedCategory.{wB} (BigModuleSheaf T.frobeniusTwistSituation)]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤))]

/-- **Arrow 1 is an isomorphism exactly when the big-site comparison is a universal arrow.**
`baseChangeArrow07QC T E` is the transpose across `- ⊗^L_{A, σ} A ⊣ σ_*` of the `σ`-semilinear
comparison, which is the big-site comparison `derivedChangeBaseBigGlobalSectionsTrans` at
`E[0]` up to isomorphisms of its source and of its target; so arrow 1 is invertible exactly when
that comparison exhibits its target as `RΓ(Cris(X/S), E) ⊗^L_{A, σ} A`, which is a property
that mentions no derived tensor product. -/
theorem isIso_baseChangeArrow07QC_iff_bijective (E : Crystalline.FCrystal T) :
    IsIso (baseChangeArrow07QC T E) ↔ ∀ Z, Function.Bijective
      (fun f : DerivedCategory.Plus.ι.obj
          ((derivedBigModuleGlobalSectionsFunctor T.frobeniusTwistSituation).obj
            ((changeBaseBigModulePullback T.frobeniusTwistSituation T.global T.specSigma
                T.twistProjection T.twistToClosedFiber_comp_closedFiberMap_specSigma
                ).rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor (BigModuleSheaf T.global) 0).obj
                ((bigModuleULift T.global).obj E.crystal)))) ⟶ Z =>
        DerivedCategory.Plus.ι.map
          ((derivedChangeBaseBigGlobalSectionsTrans (S := T.frobeniusTwistSituation)
              (S' := T.global) T.specSigma T.twistProjection
              T.twistToClosedFiber_comp_closedFiberMap_specSigma).app
            ((DerivedCategory.Plus.singleFunctor (BigModuleSheaf T.global) 0).obj
              ((bigModuleULift T.global).obj E.crystal))) ≫
          (frobeniusSigmaRestrictScalars T).map f) := by
  let N' := (bigModuleULift T.global).obj E.crystal
  let a := DerivedCategory.Plus.ι.mapIso
    (derivedRestrictModuleGlobalSectionsULiftIso T.global E.crystal).symm
  let b₁ := DerivedCategory.Plus.ι.mapIso
    ((derivedBigModuleGlobalSectionsFunctor T.frobeniusTwistSituation).mapIso
      ((changeBaseBigModulePullback T.frobeniusTwistSituation T.global T.specSigma
        T.twistProjection
        T.twistToClosedFiber_comp_closedFiberMap_specSigma).rightDerivedFunctorPlusObjSingleIso
        N'))
  let b₂ := DerivedCategory.Plus.ι.mapIso
    (derivedRestrictModuleGlobalSectionsULiftIso T.frobeniusTwistSituation
      (T.sigmaModulePullback.obj E.crystal))
  have key : sigmaTwistSemilinearArrow T E = a.hom ≫
      ((DerivedCategory.Plus.ι.map
        ((derivedChangeBaseBigGlobalSectionsTrans (S := T.frobeniusTwistSituation)
            (S' := T.global) T.specSigma T.twistProjection
            T.twistToClosedFiber_comp_closedFiberMap_specSigma).app
          ((DerivedCategory.Plus.singleFunctor (BigModuleSheaf T.global) 0).obj N')) ≫
        (frobeniusSigmaRestrictScalars T).map b₁.hom) ≫
          (frobeniusSigmaRestrictScalars T).map b₂.hom) := rfl
  refine (isIso_homEquiv_symm_iff (frobeniusDerivedBaseChangeAdjunction T)
    (sigmaTwistSemilinearArrow T E)).trans ?_
  rw [key]
  exact ((bijective_comp_map_iff_of_iso_left a _).trans
    (bijective_comp_map_iff_of_iso_right b₂ _)).trans (bijective_comp_map_iff_of_iso_right b₁ _)

end OneModel

/-- **A model of `D(Mod_A)` read as a model at the base of `X^{(1)}/S`**, which is the same ring
`A`: the base of the twist is the base of `X/S`. -/
@[instance_reducible]
def twistBaseModel (hA : HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤))) :
    HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(T.frobeniusTwistSituation.S.scheme, ⊤)) :=
  hA

/-- **Arrow 1 of the proof of [Stacks, Tag 07N5] is an isomorphism at one choice of models of the
derived categories exactly when it is one at any other.**  Here `baseChangeArrow07QC T E` is the
base change map (60.26.4.1)
`RΓ(Cris(X/S), E) ⊗^L_{A, σ} A ⟶ RΓ(Cris(X^{(1)}/S), E^{(1)})`, built from models of `D(Mod)` of
the small and big crystalline sites of `X/S` and of `X^{(1)}/S` and of `D(Mod_A)`; the two lists
`hS, hS', hB, hB', hA` and `kS, kS', kB, kB', kA` are arbitrary, in arbitrary universes. -/
theorem isIso_baseChangeArrow07QC_iff_of_models
    (hS : HasDerivedCategory.{wS} (ModuleSheaf T.global))
    (hS' : HasDerivedCategory.{wS} (ModuleSheaf T.frobeniusTwistSituation))
    (hB : HasDerivedCategory.{wB} (BigModuleSheaf T.global))
    (hB' : HasDerivedCategory.{wB} (BigModuleSheaf T.frobeniusTwistSituation))
    (hA : HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤)))
    (kS : HasDerivedCategory.{zS} (ModuleSheaf T.global))
    (kS' : HasDerivedCategory.{zS} (ModuleSheaf T.frobeniusTwistSituation))
    (kB : HasDerivedCategory.{zB} (BigModuleSheaf T.global))
    (kB' : HasDerivedCategory.{zB} (BigModuleSheaf T.frobeniusTwistSituation))
    (kA : HasDerivedCategory.{zA} (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤)))
    (E : Crystalline.FCrystal T) :
    IsIso (@baseChangeArrow07QC T hS hS' hB hB' hA E) ↔
      IsIso (@baseChangeArrow07QC T kS kS' kB kB' kA E) :=
  (@isIso_baseChangeArrow07QC_iff_bijective T hS hS' hB hB' hA E).trans
    ((bijective_derivedChangeBaseBigGlobalSectionsTrans_iff hB' hB (twistBaseModel T hA) hA kB'
        kB (twistBaseModel T kA) kA T.specSigma T.twistProjection
        T.twistToClosedFiber_comp_closedFiberMap_specSigma
        ((bigModuleULift T.global).obj E.crystal)).trans
      (@isIso_baseChangeArrow07QC_iff_bijective T kS kS' kB kB' kA E).symm)

/-- **Arrow 1 at arbitrary models versus the standard ones**: `baseChangeArrow07QC T E` built from
the models in scope is an isomorphism exactly when the one built from
`CategoryTheory.HasDerivedCategory.standard` is. -/
theorem isIso_baseChangeArrow07QC_iff_standard
    [HasDerivedCategory.{wS} (ModuleSheaf T.global)]
    [HasDerivedCategory.{wS} (ModuleSheaf T.frobeniusTwistSituation)]
    [HasDerivedCategory.{wB} (BigModuleSheaf T.global)]
    [HasDerivedCategory.{wB} (BigModuleSheaf T.frobeniusTwistSituation)]
    [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤))]
    (E : Crystalline.FCrystal T) :
    IsIso (baseChangeArrow07QC T E) ↔
      IsIso (@baseChangeArrow07QC T (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) E) :=
  isIso_baseChangeArrow07QC_iff_of_models T _ _ _ _ _ _ _ _ _ _ E

end Twist

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end

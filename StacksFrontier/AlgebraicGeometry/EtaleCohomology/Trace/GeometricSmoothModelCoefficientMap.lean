module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportDegreeZeroBridge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportCanonicalTwist

/-!
# A map on `X̄_k̄` read on the smooth model, its restriction to `X_k̄`, and the trace

Let `X` be a geometrically connected smooth curve over a field `k` with a compactification
`j : X ⟶ X̄`, `k̄` an algebraic closure, `C` the smooth projective model of `X_k̄` with
`f̄ : C ⟶ X̄_k̄`, `q = pr̄ ∘ f̄ : C ⟶ X̄` and `j_C : X_k̄ ⟶ C`, and `ψ : R →+* Λ` a morphism of
rings. For sheaves `F` of `Λ`-modules and `G` of `R`-modules on `X`, an `R`-linear map
`θ : res_ψ((j_! F)|_{X̄_k̄}) ⟶ (j_! G)|_{X̄_k̄}` on `X̄_k̄` gives

* the map `Φ_θ : res_ψ(q^{-1} j_! F) ⟶ q^{-1} j_! G` on `C`
  (`Stacks.EtaleCohomology.geometricSmoothModelCoefficientMap`): `f̄^{-1}(θ)` through
  `f̄^{-1} pr̄^{-1} ≅ q^{-1}` and `f̄^{-1} res_ψ ≅ res_ψ f̄^{-1}`;
* its restriction to `X_k̄`, `res_ψ(F|_{X_k̄}) ⟶ G|_{X_k̄}`
  (`Stacks.EtaleCohomology.compactSupportOpenRestriction`): `j_C^{-1}(Φ_θ)` through the
  identifications `j_C^{-1} q^{-1}(j_! -) ≅ (-)|_{X_k̄}` that the trace on `C` uses.

Under the smooth model `H²_c(X_k̄, -) ≅ H²(C, q^{-1}(j_! -))` the map
`H²_c(X_k̄, F) ⟶ H²_c(X_k̄, G)` induced by `θ`
(`Stacks.EtaleCohomology.galoisCompactSupportRestrictScalarsMapOfBar`) is `H²(C, Φ_θ)` after the
coefficient change, and so the trace on `C` carries it to `Γ(X_k̄, -)` of the restriction.

## Main definitions

* `geometricSmoothModelCoefficientMap`.
* `compactSupportOpenRestriction`.

## Main results

* `galoisCompactSupportSmoothModelInverseImageEquiv_eq_restriction`.
* `galoisCompactSupportSmoothModelInverseImageEquiv_restrictScalarsMapOfBar`.
* `geometricSmoothModelRestrictionTrace_restrictScalarsMapOfBar`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.Frobenius

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.EtaleCohomology.etaleModulesEnoughInjectivesZeroTraceTwist
  Stacks.EtaleCohomology.moduleCatHasColimitsOfSizeSmallEtale
  Stacks.EtaleCohomology.hasGlobalSectionsFunctorSmallEtaleModuleCat

namespace Stacks.EtaleCohomology

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
  [GeometricallyConnected f] (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar]

section Restriction

/-- **`H²_c(X_k̄, F) ≅ H²(C, q^{-1}(j_! F))` without `q^{-1}(j_! F) ≅ j_{C!}(F|_{X_k̄})`**: it is
the restriction map `(j_! F)|_{X̄_k̄} ⟶ f̄_* q^{-1}(j_! F)` on `H²(X̄_k̄, -)`, followed by
`H²(X̄_k̄, f̄_* -) ≅ H²(C, -)`. -/
theorem galoisCompactSupportSmoothModelInverseImageEquiv_eq_restriction (S : Type) [Ring S]
    (F : EtaleModules.{u, 0} S X) (i : ℤ)
    (x : galoisCompactSupportCohomologyGroup.{u, 0} S f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) i) :
    galoisCompactSupportSmoothModelInverseImageEquiv f j kbar S F i x =
      (integralDirectImageCohomologyIso S (geometricSmoothModel f j kbar).fb _ i).hom.hom
        ((((etaleModuleGlobalSections.{u, 0} S (pullback j.toBase (specAlgebraMap k
            kbar))).rightDerivedPlus i).map (geometricSmoothModelRestriction f j kbar S F)).hom
          ((galoisCompactSupportSingleIso f j kbar S F i).hom.hom x)) := by
  rw [galoisCompactSupportSmoothModelInverseImageEquiv_apply,
    galoisCompactSupportSmoothModelIso_hom_eq_restriction]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [← LinearMap.comp_apply (((etaleModuleGlobalSections.{u, 0} S
      (geometricSmoothModel f j kbar).Vb).rightDerivedPlus i).map
        (geometricSmoothModelInverseImageIso f j kbar S F).inv).hom, ← ModuleCat.hom_comp,
    ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, ModuleCat.hom_id,
    LinearMap.id_apply]

variable {R Λ : Type} [Ring R] [Ring Λ] (ψ : R →+* Λ)

/-- **`f̄^{-1} res_ψ((j_! F)|_{X̄_k̄}) ≅ res_ψ(q^{-1} j_! F)`** on the smooth model `C`:
`f̄^{-1} res_ψ ≅ res_ψ f̄^{-1}` and `f̄^{-1} pr̄^{-1} ≅ q^{-1}`. -/
def geometricSmoothModelRestrictScalarsInverseImageIso (F : EtaleModules.{u, 0} Λ X) :
    (etaleModuleInverseImage.{u, 0} R (geometricSmoothModel f j kbar).fb).obj
        ((etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))) ≅
      (etaleModuleRestrictScalars ψ (geometricSmoothModel f j kbar).Vb).obj
        ((etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) :=
  (etaleModuleInverseImageRestrictScalars ψ (geometricSmoothModel f j kbar).fb).app
      ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) ≪≫
    (etaleModuleRestrictScalars ψ (geometricSmoothModel f j kbar).Vb).mapIso
      ((selfMapRestrictionIso.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))
        (geometricSmoothModel f j kbar).fb (geometricSmoothModelProj f j kbar) rfl).app
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))

/-- **The map `Φ_θ : res_ψ(q^{-1} j_! F) ⟶ q^{-1} j_! G` on the smooth model `C`** induced by
`θ : res_ψ((j_! F)|_{X̄_k̄}) ⟶ (j_! G)|_{X̄_k̄}`: `res_ψ q^{-1} ≅ f̄^{-1} res_ψ pr̄^{-1}`
(`Stacks.EtaleCohomology.geometricSmoothModelRestrictScalarsInverseImageIso`), `f̄^{-1}(θ)` and
`f̄^{-1} pr̄^{-1} ≅ q^{-1}`. -/
def geometricSmoothModelCoefficientMap (F : EtaleModules.{u, 0} Λ X) (G : EtaleModules.{u, 0} R X)
    (θ : (etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) ⟶
      (etaleModuleInverseImage.{u, 0} R (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G)) :
    (etaleModuleRestrictScalars ψ (geometricSmoothModel f j kbar).Vb).obj
        ((etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) ⟶
      (etaleModuleInverseImage.{u, 0} R (geometricSmoothModelProj f j kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G) :=
  (geometricSmoothModelRestrictScalarsInverseImageIso f j kbar ψ F).inv ≫
    (etaleModuleInverseImage.{u, 0} R (geometricSmoothModel f j kbar).fb).map θ ≫
    (selfMapRestrictionIso.{u, 0} R (pullback.fst j.toBase (specAlgebraMap k kbar))
        (geometricSmoothModel f j kbar).fb (geometricSmoothModelProj f j kbar) rfl).hom.app
      ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G)

/-- **The restriction to `X_k̄` of `θ : res_ψ((j_! F)|_{X̄_k̄}) ⟶ (j_! G)|_{X̄_k̄}`**, read on the
smooth model: `j_C^{-1}` of `Stacks.EtaleCohomology.geometricSmoothModelCoefficientMap`, through
`j_C^{-1} q^{-1}(j_! -) ≅ (-)|_{X_k̄}`
(`Stacks.EtaleCohomology.geometricSmoothModelInverseImageRestrictionIso`). -/
def compactSupportOpenRestriction (F : EtaleModules.{u, 0} Λ X) (G : EtaleModules.{u, 0} R X)
    (θ : (etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) ⟶
      (etaleModuleInverseImage.{u, 0} R (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G)) :
    (etaleModuleRestrictScalars ψ (pullback f (specAlgebraMap k kbar))).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj F) ⟶
      (etaleModuleInverseImage.{u, 0} R (pullback.fst f (specAlgebraMap k kbar))).obj G :=
  (etaleModuleRestrictScalars ψ (pullback f (specAlgebraMap k kbar))).map
      (geometricSmoothModelInverseImageRestrictionIso f j kbar Λ F).inv ≫
    (restrictionRestrictScalarsIso ψ (geometricSmoothModel f j kbar).j _).hom ≫
    (etaleModuleRestriction.{u, 0} R (geometricSmoothModel f j kbar).j).map
      (geometricSmoothModelCoefficientMap f j kbar ψ F G θ) ≫
    (geometricSmoothModelInverseImageRestrictionIso f j kbar R G).hom

/-- **`Φ_θ` is compatible with the restriction to `X_k̄`** (the hypothesis of
`Stacks.EtaleCohomology.curveExtensionByZeroRestrictionTrace_restrictScalars`). -/
theorem geometricSmoothModelCoefficientMap_restriction (F : EtaleModules.{u, 0} Λ X)
    (G : EtaleModules.{u, 0} R X)
    (θ : (etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) ⟶
      (etaleModuleInverseImage.{u, 0} R (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G)) :
    (restrictionRestrictScalarsIso ψ (geometricSmoothModel f j kbar).j _).hom ≫
        (etaleModuleRestriction.{u, 0} R (geometricSmoothModel f j kbar).j).map
          (geometricSmoothModelCoefficientMap f j kbar ψ F G θ) ≫
        (geometricSmoothModelInverseImageRestrictionIso f j kbar R G).hom =
      (etaleModuleRestrictScalars ψ (pullback f (specAlgebraMap k kbar))).map
          (geometricSmoothModelInverseImageRestrictionIso f j kbar Λ F).hom ≫
        compactSupportOpenRestriction f j kbar ψ F G θ := by
  rw [compactSupportOpenRestriction, ← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **`Φ_θ` is the map on `C` matching `θ` under the restriction maps** `N ⟶ f̄_* q^{-1} N`
(`Stacks.EtaleCohomology.geometricSmoothModelRestriction`): `res_ψ` of the restriction map for
`F` followed by `f̄_* Φ_θ` is `θ` followed by the restriction map for `G`. -/
theorem restrictScalars_geometricSmoothModelRestriction_comp (F : EtaleModules.{u, 0} Λ X)
    (G : EtaleModules.{u, 0} R X)
    (θ : (etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) ⟶
      (etaleModuleInverseImage.{u, 0} R (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G)) :
    (etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).map
        (geometricSmoothModelRestriction f j kbar Λ F) ≫
      (etaleModuleDirectImage.{u, 0} R (geometricSmoothModel f j kbar).fb).map
        (geometricSmoothModelCoefficientMap f j kbar ψ F G θ) =
    θ ≫ geometricSmoothModelRestriction f j kbar R G := by
  have hu : (etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).map
      ((etaleModuleInverseImageAdj.{u, 0} Λ (geometricSmoothModel f j kbar).fb).unit.app
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))) =
      (etaleModuleInverseImageAdj.{u, 0} R (geometricSmoothModel f j kbar).fb).unit.app
          ((etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).obj
            ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
              ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))) ≫
        (etaleModuleDirectImage.{u, 0} R (geometricSmoothModel f j kbar).fb).map
          ((etaleModuleInverseImageRestrictScalars ψ (geometricSmoothModel f j kbar).fb).hom.app
            ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
              ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))) :=
    coefficientSheafPullbackTwoSquare_unit _ _ _ _ _
  have hn :=
    (etaleModuleInverseImageAdj.{u, 0} R (geometricSmoothModel f j kbar).fb).unit.naturality θ
  simp only [Functor.id_map, Functor.comp_map] at hn
  have e0 := selfMapRestriction_app.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))
    (geometricSmoothModel f j kbar).fb (geometricSmoothModelProj f j kbar) rfl
    ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)
  have e0' := selfMapRestriction_app.{u, 0} R (pullback.fst j.toBase (specAlgebraMap k kbar))
    (geometricSmoothModel f j kbar).fb (geometricSmoothModelProj f j kbar) rfl
    ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G)
  have hd : ∀ {A B : EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb} (g : A ⟶ B),
      (etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).map
          ((etaleModuleDirectImage.{u, 0} Λ (geometricSmoothModel f j kbar).fb).map g) =
        (etaleModuleDirectImage.{u, 0} R (geometricSmoothModel f j kbar).fb).map
          ((etaleModuleRestrictScalars ψ (geometricSmoothModel f j kbar).Vb).map g) :=
    fun _ => rfl
  have e1 : (etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).map
        (geometricSmoothModelRestriction f j kbar Λ F) =
      (etaleModuleInverseImageAdj.{u, 0} R (geometricSmoothModel f j kbar).fb).unit.app
          ((etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).obj
            ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
              ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))) ≫
        (etaleModuleDirectImage.{u, 0} R (geometricSmoothModel f j kbar).fb).map
          (geometricSmoothModelRestrictScalarsInverseImageIso f j kbar ψ F).hom :=
    (congrArg (etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).map
      e0).trans
      ((Functor.map_comp _ _ _).trans ((congrArg (· ≫ _) hu).trans
        ((congrArg (_ ≫ ·) (hd _)).trans ((Category.assoc _ _ _).trans
        (congrArg (_ ≫ ·) (Functor.map_comp
          (etaleModuleDirectImage.{u, 0} R (geometricSmoothModel f j kbar).fb) _ _).symm)))))
  have hΦ : (geometricSmoothModelRestrictScalarsInverseImageIso f j kbar ψ F).hom ≫
      geometricSmoothModelCoefficientMap f j kbar ψ F G θ =
      (etaleModuleInverseImage.{u, 0} R (geometricSmoothModel f j kbar).fb).map θ ≫
        (selfMapRestrictionIso.{u, 0} R (pullback.fst j.toBase (specAlgebraMap k kbar))
          (geometricSmoothModel f j kbar).fb (geometricSmoothModelProj f j kbar) rfl).hom.app
            ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G) :=
    (geometricSmoothModelRestrictScalarsInverseImageIso f j kbar ψ F).hom_inv_id_assoc _
  refine (congrArg (· ≫ _) e1).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) ((Functor.map_comp
    (etaleModuleDirectImage.{u, 0} R (geometricSmoothModel f j kbar).fb) _ _).symm.trans
      ((congrArg (etaleModuleDirectImage.{u, 0} R (geometricSmoothModel f j kbar).fb).map hΦ).trans
        (Functor.map_comp _ _ _)))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) hn.symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (θ ≫ ·) e0'.symm

end Restriction

section Transfer

/-- `res_ℤ Hⁱ(-, -) ≅ Hⁱ(-, res_ℤ -)` on elements, naturally. -/
theorem rightDerivedPlusRestrictScalarsIntIso_hom_map_apply {S : Type} [Ring S] (Y : Scheme.{u})
    {N N' : EtaleModules.{u, 0} S Y} (g : N ⟶ N') (i : ℤ)
    (z : ((etaleModuleGlobalSections.{u, 0} S Y).rightDerivedPlus i).obj N) :
    (rightDerivedPlusRestrictScalarsIntIso Y N' i).hom.hom
        ((((etaleModuleGlobalSections.{u, 0} S Y).rightDerivedPlus i).map g).hom z) =
      (((etaleModuleGlobalSections.{u, 0} ℤ Y).rightDerivedPlus i).map
        ((etaleModuleRestrictScalars (Int.castRingHom S) Y).map g)).hom
        ((rightDerivedPlusRestrictScalarsIntIso Y N i).hom.hom z) :=
  congrArg (fun φ => φ.hom z) (rightDerivedPlusRestrictScalarsIntIso_hom_naturality Y g i)

/-- `Hⁱ(B, g_* H) ≅ Hⁱ(A, H)` and `res_ℤ` on elements. -/
theorem integralDirectImageCohomologyIso_hom_restrictScalarsInt_apply {S : Type} [Ring S]
    {A B : Scheme.{u}} (g : A ⟶ B) [IsIntegralHom g] (H : EtaleModules.{u, 0} S A) (i : ℤ)
    (w : ((etaleModuleGlobalSections.{u, 0} S B).rightDerivedPlus i).obj
      ((etaleModuleDirectImage.{u, 0} S g).obj H)) :
    (rightDerivedPlusRestrictScalarsIntIso A H i).hom.hom
        ((integralDirectImageCohomologyIso S g H i).hom.hom w) =
      (integralDirectImageCohomologyIso ℤ g
          ((etaleModuleRestrictScalars (Int.castRingHom S) A).obj H) i).hom.hom
        ((rightDerivedPlusRestrictScalarsIntIso B
            ((etaleModuleDirectImage.{u, 0} S g).obj H) i).hom.hom w) :=
  congrArg (fun φ => φ.hom w) (integralDirectImageCohomologyIso_hom_restrictScalarsInt g H i)

/-- `Hⁱ(B, g_* H) ≅ Hⁱ(A, H)` on elements, naturally. -/
theorem integralDirectImageCohomologyIso_hom_map_apply {S : Type} [Ring S] {A B : Scheme.{u}}
    (g : A ⟶ B) [IsIntegralHom g] {H H' : EtaleModules.{u, 0} S A} (h : H ⟶ H') (i : ℤ)
    (w : ((etaleModuleGlobalSections.{u, 0} S B).rightDerivedPlus i).obj
      ((etaleModuleDirectImage.{u, 0} S g).obj H)) :
    (((etaleModuleGlobalSections.{u, 0} S A).rightDerivedPlus i).map h).hom
        ((integralDirectImageCohomologyIso S g H i).hom.hom w) =
      (integralDirectImageCohomologyIso S g H' i).hom.hom
        ((((etaleModuleGlobalSections.{u, 0} S B).rightDerivedPlus i).map
          ((etaleModuleDirectImage.{u, 0} S g).map h)).hom w) :=
  (congrArg (fun φ => φ.hom w) (integralDirectImageCohomologyIso_hom_naturality S g h i)).symm

/-- `Stacks.EtaleCohomology.integralDirectImageCohomologyIso_hom_map_apply` over `ℤ` at `res_ℤ H`,
for a class read through `res_ℤ (g_* H) = g_* (res_ℤ H)`. -/
theorem integralDirectImageCohomologyIso_hom_map_restrictScalarsInt_apply {S : Type} [Ring S]
    {A B : Scheme.{u}} (g : A ⟶ B) [IsIntegralHom g] (H : EtaleModules.{u, 0} S A)
    {H'' : EtaleModules.{u, 0} ℤ A}
    (h : (etaleModuleRestrictScalars (Int.castRingHom S) A).obj H ⟶ H'') (i : ℤ)
    (w : ((etaleModuleGlobalSections.{u, 0} ℤ B).rightDerivedPlus i).obj
      ((etaleModuleRestrictScalars (Int.castRingHom S) B).obj
        ((etaleModuleDirectImage.{u, 0} S g).obj H))) :
    (((etaleModuleGlobalSections.{u, 0} ℤ A).rightDerivedPlus i).map h).hom
        ((integralDirectImageCohomologyIso ℤ g
          ((etaleModuleRestrictScalars (Int.castRingHom S) A).obj H) i).hom.hom w) =
      (integralDirectImageCohomologyIso ℤ g H'' i).hom.hom
        ((((etaleModuleGlobalSections.{u, 0} ℤ B).rightDerivedPlus i).map
          ((etaleModuleDirectImage.{u, 0} ℤ g).map h)).hom w) :=
  integralDirectImageCohomologyIso_hom_map_apply g h i w

variable {R Λ : Type} [Ring R] [Ring Λ] (ψ : R →+* Λ)

/-- **Transfer of a coefficient change along an integral morphism.** Let `g : A ⟶ B` be integral,
`r : P ⟶ g_* H` over `Λ`, `r' : P' ⟶ g_* H'` over `R`, and `θ : res_ψ P ⟶ P'`,
`Φ : res_ψ H ⟶ H'` over `R` with `res_ψ(r) ≫ g_*(Φ) = θ ≫ r'`. Then, through
`Hⁱ(B, g_* -) ≅ Hⁱ(A, -)` and the coefficient changes `Hⁱ(-, N) ≃+ Hⁱ(-, res_ψ N)`,
`Hⁱ(θ) ≫ Hⁱ(r')` on `B` matches `Hⁱ(Φ)` on `A`. -/
theorem integralDirectImageCohomologyIso_restrictScalars_transfer {A B S : Scheme.{u}} (g : A ⟶ B)
    [IsIntegralHom g] {P : EtaleModules.{u, 0} Λ B} {P' : EtaleModules.{u, 0} R B}
    (Q : EtaleModules.{u, 0} Λ S ⥤ EtaleModules.{u, 0} Λ A)
    (Q' : EtaleModules.{u, 0} R S ⥤ EtaleModules.{u, 0} R A) (M : EtaleModules.{u, 0} Λ S)
    (M' : EtaleModules.{u, 0} R S)
    (r : P ⟶ (Q ⋙ etaleModuleDirectImage.{u, 0} Λ g).obj M)
    (r' : P' ⟶ (Q' ⋙ etaleModuleDirectImage.{u, 0} R g).obj M')
    (θ : (etaleModuleRestrictScalars ψ B).obj P ⟶ P')
    (Φ : (etaleModuleRestrictScalars ψ A).obj (Q.obj M) ⟶ Q'.obj M')
    (hsq : (etaleModuleRestrictScalars ψ B).map r ≫ (etaleModuleDirectImage.{u, 0} R g).map Φ =
      θ ≫ r') (i : ℕ)
    (y : ((etaleModuleGlobalSections.{u, 0} Λ B).rightDerivedPlus (i : ℤ)).obj P) :
    (integralDirectImageCohomologyIso R g (Q'.obj M') (i : ℤ)).hom.hom
        ((((etaleModuleGlobalSections.{u, 0} R B).rightDerivedPlus (i : ℤ)).map r').hom
          ((((etaleModuleGlobalSections.{u, 0} R B).rightDerivedPlus (i : ℤ)).map θ).hom
            (etaleModuleCohomologyRestrictScalars ψ B P i y))) =
      (((etaleModuleGlobalSections.{u, 0} R A).rightDerivedPlus (i : ℤ)).map Φ).hom
        (etaleModuleCohomologyRestrictScalars ψ A (Q.obj M) i
          ((integralDirectImageCohomologyIso Λ g (Q.obj M) (i : ℤ)).hom.hom
            ((((etaleModuleGlobalSections.{u, 0} Λ B).rightDerivedPlus (i : ℤ)).map r).hom
              y))) := by
  apply (ModuleCat.mono_iff_injective
    (rightDerivedPlusRestrictScalarsIntIso A (Q'.obj M') (i : ℤ)).hom).1 inferInstance
  rw [integralDirectImageCohomologyIso_hom_restrictScalarsInt_apply,
    rightDerivedPlusRestrictScalarsIntIso_hom_map_apply,
    rightDerivedPlusRestrictScalarsIntIso_hom_map_apply,
    rightDerivedPlusRestrictScalarsIntIso_restrictScalars,
    rightDerivedPlusRestrictScalarsIntIso_hom_map_apply,
    rightDerivedPlusRestrictScalarsIntIso_restrictScalars,
    integralDirectImageCohomologyIso_hom_restrictScalarsInt_apply,
    rightDerivedPlusRestrictScalarsIntIso_hom_map_apply,
    integralDirectImageCohomologyIso_hom_map_restrictScalarsInt_apply,
    integralDirectImageCohomologyIso_hom_map_apply]
  refine congrArg (integralDirectImageCohomologyIso ℤ g
    ((etaleModuleRestrictScalars (Int.castRingHom R) A).obj (Q'.obj M')) (i : ℤ)).hom.hom ?_
  have hZ : (restrictScalarsIntCompIso ψ B P).hom ≫
      (etaleModuleRestrictScalars (Int.castRingHom R) B).map θ ≫
      (etaleModuleRestrictScalars (Int.castRingHom R) B).map r' =
    (etaleModuleRestrictScalars (Int.castRingHom Λ) B).map r ≫
      (etaleModuleDirectImage.{u, 0} ℤ g).map (restrictScalarsIntCompIso ψ A (Q.obj M)).hom ≫
      (etaleModuleDirectImage.{u, 0} ℤ g).map
        ((etaleModuleRestrictScalars (Int.castRingHom R) A).map Φ) := by
    have h' := fun U x => ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app U) hsq) x
    ext U x
    exact (h' U x).symm
  have hM := ((congrArg
      (((etaleModuleGlobalSections.{u, 0} ℤ B).rightDerivedPlus (i : ℤ)).map
        (restrictScalarsIntCompIso ψ B P).hom ≫ ·)
      (((etaleModuleGlobalSections.{u, 0} ℤ B).rightDerivedPlus (i : ℤ)).map_comp _ _).symm).trans
      (((etaleModuleGlobalSections.{u, 0} ℤ B).rightDerivedPlus (i : ℤ)).map_comp _ _).symm).trans
    ((congrArg ((etaleModuleGlobalSections.{u, 0} ℤ B).rightDerivedPlus (i : ℤ)).map hZ).trans
      ((((etaleModuleGlobalSections.{u, 0} ℤ B).rightDerivedPlus (i : ℤ)).map_comp _ _).trans
        (congrArg (((etaleModuleGlobalSections.{u, 0} ℤ B).rightDerivedPlus (i : ℤ)).map
            ((etaleModuleRestrictScalars (Int.castRingHom Λ) B).map r) ≫ ·)
          (((etaleModuleGlobalSections.{u, 0} ℤ B).rightDerivedPlus (i : ℤ)).map_comp _ _))))
  have h := congrArg (fun φ => ModuleCat.Hom.hom φ
    ((rightDerivedPlusRestrictScalarsIntIso B P (i : ℤ)).hom.hom y)) hM
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- **The map on `H²_c` induced by `θ` is `H²(C, Φ_θ)` on the smooth model**: under
`H²_c(X_k̄, -) ≅ H²(C, q^{-1}(j_! -))`
(`Stacks.EtaleCohomology.galoisCompactSupportSmoothModelInverseImageEquiv`) over `Λ` and over `R`,
`Stacks.EtaleCohomology.galoisCompactSupportRestrictScalarsMapOfBar` is the coefficient change
`H²(C, -) ≃+ H²(C, res_ψ -)` followed by `H²(C, Φ_θ)`. -/
theorem galoisCompactSupportSmoothModelInverseImageEquiv_restrictScalarsMapOfBar
    (F : EtaleModules.{u, 0} Λ X) (G : EtaleModules.{u, 0} R X)
    (θ : (etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) ⟶
      (etaleModuleInverseImage.{u, 0} R (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G))
    (x : galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) ((2 : ℕ) : ℤ)) :
    galoisCompactSupportSmoothModelInverseImageEquiv f j kbar R G ((2 : ℕ) : ℤ)
        (galoisCompactSupportRestrictScalarsMapOfBar f j kbar ψ F G θ x) =
      (((etaleModuleGlobalSections.{u, 0} R (geometricSmoothModel f j kbar).Vb).rightDerivedPlus
          ((2 : ℕ) : ℤ)).map (geometricSmoothModelCoefficientMap f j kbar ψ F G θ)).hom
        (etaleModuleCohomologyRestrictScalars ψ (geometricSmoothModel f j kbar).Vb _ 2
          (galoisCompactSupportSmoothModelInverseImageEquiv f j kbar Λ F ((2 : ℕ) : ℤ) x)) := by
  rw [galoisCompactSupportSmoothModelInverseImageEquiv_eq_restriction,
    galoisCompactSupportSmoothModelInverseImageEquiv_eq_restriction,
    galoisCompactSupportRestrictScalarsMapOfBar_apply]
  exact integralDirectImageCohomologyIso_restrictScalars_transfer ψ
    (geometricSmoothModel f j kbar).fb
    (etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar))
    (etaleModuleInverseImage.{u, 0} R (geometricSmoothModelProj f j kbar))
    ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)
    ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G)
    (geometricSmoothModelRestriction f j kbar Λ F) (geometricSmoothModelRestriction f j kbar R G) θ
    (geometricSmoothModelCoefficientMap f j kbar ψ F G θ)
    (restrictScalars_geometricSmoothModelRestriction_comp f j kbar ψ F G θ) 2 _

/-- **The trace on the smooth model carries the map induced by `θ` to `Γ(X_k̄, -)` of its
restriction to `X_k̄`.** For `ψ : R →+* Λ` between finite rings of the same order `n`, invertible
in `k̄`, a primitive `n`-th root of unity `ζ`, and `F`, `G` whose restrictions to `X_k̄` are
constant on finite global sections, the trace `H²(C, q^{-1}(j_! G)) ≅ Γ(X_k̄, G|_{X_k̄})` over `R`
of the image under `H²_c(X_k̄, F) ⟶ H²_c(X_k̄, G)`
(`Stacks.EtaleCohomology.galoisCompactSupportRestrictScalarsMapOfBar`) is `Γ(X_k̄, -)` of
`Stacks.EtaleCohomology.compactSupportOpenRestriction` applied to the trace over `Λ`. -/
theorem geometricSmoothModelRestrictionTrace_restrictScalarsMapOfBar [Fintype R] [Fintype Λ]
    (hcard : Fintype.card R = Fintype.card Λ) (hn : IsUnit ((Fintype.card Λ : ℕ) : kbar))
    {ζ : kbar} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ))
    (hnR : IsUnit ((Fintype.card R : ℕ) : kbar)) (hζR : IsPrimitiveRoot ζ (Fintype.card R))
    (F : EtaleModules.{u, 0} Λ X) (G : EtaleModules.{u, 0} R X)
    (θ : (etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) ⟶
      (etaleModuleInverseImage.{u, 0} R (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G))
    (hG : IsIso ((constantSheafΓAdj (pullback f (specAlgebraMap k kbar)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).counit.app
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj F)))
    (hE : Finite ((etaleModuleGlobalSections.{u, 0} Λ (pullback f (specAlgebraMap k kbar))).obj
      ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj F)))
    (hG' : IsIso ((constantSheafΓAdj (pullback f (specAlgebraMap k kbar)).smallEtaleTopology
      (ModuleCat.{u + 1} R)).counit.app
        ((etaleModuleInverseImage.{u, 0} R (pullback.fst f (specAlgebraMap k kbar))).obj G)))
    (hE' : Finite ((etaleModuleGlobalSections.{u, 0} R (pullback f (specAlgebraMap k kbar))).obj
      ((etaleModuleInverseImage.{u, 0} R (pullback.fst f (specAlgebraMap k kbar))).obj G)))
    (x : galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) ((2 : ℕ) : ℤ)) :
    curveExtensionByZeroRestrictionTrace (geometricSmoothModel f j kbar).q R hnR hζR
        (geometricSmoothModel f j kbar).j (geometricSmoothModel f j kbar).finite_compl
        ((etaleModuleInverseImage.{u, 0} R (geometricSmoothModelProj f j kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G))
        ((etaleModuleInverseImage.{u, 0} R (pullback.fst f (specAlgebraMap k kbar))).obj G)
        (geometricSmoothModelInverseImageRestrictionIso f j kbar R G) hG' hE'
        (galoisCompactSupportSmoothModelInverseImageEquiv f j kbar R G ((2 : ℕ) : ℤ)
          (galoisCompactSupportRestrictScalarsMapOfBar f j kbar ψ F G θ x)) =
      globalSectionsRestrictScalarsAddHom ψ (pullback f (specAlgebraMap k kbar))
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj F)
        ((etaleModuleInverseImage.{u, 0} R (pullback.fst f (specAlgebraMap k kbar))).obj G)
        (compactSupportOpenRestriction f j kbar ψ F G θ)
        (curveExtensionByZeroRestrictionTrace (geometricSmoothModel f j kbar).q Λ hn hζ
          (geometricSmoothModel f j kbar).j (geometricSmoothModel f j kbar).finite_compl
          ((etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj F)
          (geometricSmoothModelInverseImageRestrictionIso f j kbar Λ F) hG hE
          (galoisCompactSupportSmoothModelInverseImageEquiv f j kbar Λ F ((2 : ℕ) : ℤ) x)) := by
  rw [galoisCompactSupportSmoothModelInverseImageEquiv_restrictScalarsMapOfBar]
  exact curveExtensionByZeroRestrictionTrace_restrictScalars (geometricSmoothModel f j kbar).q ψ
    hn hζ hnR hζR (geometricSmoothModel f j kbar).j (geometricSmoothModel f j kbar).finite_compl
    hcard
    _ _ (geometricSmoothModelInverseImageRestrictionIso f j kbar Λ F) hG hE _ _
    (geometricSmoothModelInverseImageRestrictionIso f j kbar R G) hG' hE'
    (geometricSmoothModelCoefficientMap f j kbar ψ F G θ)
    (compactSupportOpenRestriction f j kbar ψ F G θ)
    (geometricSmoothModelCoefficientMap_restriction f j kbar ψ F G θ) _

end Transfer


end Stacks.EtaleCohomology

end

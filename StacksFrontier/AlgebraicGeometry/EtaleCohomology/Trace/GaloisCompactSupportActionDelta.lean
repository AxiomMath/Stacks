module

public import StacksFrontier.Homology.DerivedIndexing.TwistDeltaHom
public import StacksFrontier.Homology.DerivedIndexing.CompIsoOfIsoCommShift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafCompactSupportDelta
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSmoothModelGaloisCompat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricSmoothModelInverseImageNatural

/-!
# The Galois action on `H^q_c(X_k̄, ℱ_ρ)` commutes with the connecting morphisms

Let `X` be a geometrically connected smooth curve over a field `k`, `j : X ⟶ X̄` a
compactification, `k̄` an algebraically closed extension of `k`, `C` the smooth projective model of
`X_k̄` and `σ ∈ Aut_k(k̄)`. The action of `σ` on `H^q_c(X_k̄, ℱ) = H^q(C, j_{C!}(ℱ|_{X_k̄}))`
(`Stacks.EtaleCohomology.geometricSmoothModelGaloisAction`, the pullback along
`s̃_σ = id_{C'} × Spec σ`) is, for `ℱ = ℱ_ρ` attached to a representation `ρ` of `π₁(X, x̄)`, an
endomorphism of the cohomological δ-functor `ρ ↦ H^q(C, j_{C!}(ℱ_ρ|_{X_k̄}))`: it commutes with
the connecting morphisms of short exact sequences of representations.

It is the endomorphism attached to a twist (`Stacks.DerivedIndexing.twistDeltaHom`): the
linearization `j_{C!}(ℱ|_{X_k̄}) ⟶ (s̃_σ)_* j_{C!}(ℱ|_{X_k̄})` of the pullback of `j_! ℱ` along
`q : C ⟶ X̄` (`Stacks.EtaleCohomology.selfMapTwist`), natural in `ℱ`, followed by
`RΓ(C, -) ∘ R(s̃_σ)_* = RΓ(C, -)`, which commutes with the shift
(`Stacks.DerivedIndexing.natTransCommShift_rightDerivedFunctorPlusCompIsoOfIso_inv`).

## Main definitions

* `AlgebraicGeometry.compactSupportRepresentationGaloisTwist` — the twist, natural in `ρ`.
* `AlgebraicGeometry.compactSupportRepresentationCohomologyGalois` — the action of `σ` as an
  endomorphism of the δ-functor `ρ ↦ H^q(C, j_{C!}(ℱ_ρ|_{X_k̄}))`.

## Main results

* `AlgebraicGeometry.compactSupportRepresentationCohomologyGalois_app_app` — in degree `q` it is
  `Stacks.EtaleCohomology.geometricSmoothModelGaloisAction`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

section Twist

attribute [local instance high] etaleModules_hasSheafify

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
  [GeometricallyConnected f] (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] (Λ : Type) [Ring Λ] (σ : kbar ≃ₐ[k] kbar)

/-- **The Galois twist of `j_{C!}(F|_{X_k̄})`**: the linearization along `s̃_σ` of the pullback of
`j_! F` along `q : C ⟶ X̄` (`Stacks.EtaleCohomology.selfMapTwist`), read through
`q^{-1}(j_! F) ≅ j_{C!}(F|_{X_k̄})`. -/
def geometricSmoothModelGaloisTwistApp (F : EtaleModules.{u, 0} Λ X) :
    (etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj F) ⟶
      (etaleModuleDirectImage.{u, 0} Λ (geometricSmoothModelGaloisAut f j kbar σ)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).obj
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj F)) :=
  (geometricSmoothModelInverseImageIso f j kbar Λ F).inv ≫
    (selfMapTwist.{u, 0} Λ (geometricSmoothModelProj f j kbar)
        (geometricSmoothModelGaloisAut f j kbar σ)
        (geometricSmoothModelGaloisAut_comp_proj f j kbar σ)).app
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F) ≫
    (etaleModuleDirectImage.{u, 0} Λ (geometricSmoothModelGaloisAut f j kbar σ)).map
      (geometricSmoothModelInverseImageIso f j kbar Λ F).hom

/-- The Galois twist is natural in the sheaf. -/
theorem geometricSmoothModelGaloisTwistApp_naturality {F F' : EtaleModules.{u, 0} Λ X}
    (g : F ⟶ F') :
    (etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).map
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).map g) ≫
      geometricSmoothModelGaloisTwistApp f j kbar Λ σ F' =
    geometricSmoothModelGaloisTwistApp f j kbar Λ σ F ≫
      (etaleModuleDirectImage.{u, 0} Λ (geometricSmoothModelGaloisAut f j kbar σ)).map
        ((etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).map
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).map g)) := by
  have hi := geometricSmoothModelInverseImageIso_hom_naturality f j kbar Λ g
  have hi' : (etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).map
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).map g) ≫
      (geometricSmoothModelInverseImageIso f j kbar Λ F').inv =
    (geometricSmoothModelInverseImageIso f j kbar Λ F).inv ≫
      (etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).map
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map g) := by
    rw [Iso.eq_inv_comp, ← Category.assoc]
    refine Eq.trans ?_ (Category.comp_id _)
    rw [← Iso.hom_inv_id (geometricSmoothModelInverseImageIso f j kbar Λ F'), ← Category.assoc]
    exact congrArg (· ≫ _) hi.symm
  have ht := (selfMapTwist.{u, 0} Λ (geometricSmoothModelProj f j kbar)
      (geometricSmoothModelGaloisAut f j kbar σ)
      (geometricSmoothModelGaloisAut_comp_proj f j kbar σ)).naturality
    ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map g)
  simp only [Functor.comp_map] at ht
  dsimp only [geometricSmoothModelGaloisTwistApp]
  simp only [Category.assoc]
  refine ((reassoc_of% hi') _).trans (congrArg (_ ≫ ·) ?_)
  refine ((reassoc_of% ht) _).trans (congrArg (_ ≫ ·) ?_)
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg _ hi

section Derived

attribute [local instance] HasDerivedCategory.standard Functor.commShiftRightDerivedFunctorPlus

/-- Enough injectives for sheaves of `Λ`-modules at coefficient universe `0`, pinned. -/
local instance (priority := 3000) etaleModulesEnoughInjectivesGaloisDelta (Λ : Type) [Ring Λ]
    (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

/-- **`RΓ(C, -) ∘ R(s̃_σ)_* = RΓ(C, -)`** on the smooth projective model, for `s̃_σ` integral. -/
abbrev geometricSmoothModelGaloisDerivedComparison :
    (etaleModuleDirectImage.{u, 0} Λ
        (geometricSmoothModelGaloisAut f j kbar σ)).rightDerivedFunctorPlus ⋙
      (etaleModuleGlobalSections.{u, 0} Λ
          (geometricSmoothModel f j kbar).Vb).rightDerivedFunctorPlus ⟶
    (etaleModuleGlobalSections.{u, 0} Λ
        (geometricSmoothModel f j kbar).Vb).rightDerivedFunctorPlus :=
  (etaleModuleDerivedGlobalSectionsCompIso.{u, 0} Λ (geometricSmoothModelGaloisAut f j kbar σ)).inv

/-- `RΓ(C, -) ∘ R(s̃_σ)_* = RΓ(C, -)` commutes with the shift. -/
instance natTransCommShift_geometricSmoothModelGaloisDerivedComparison :
    NatTrans.CommShift (geometricSmoothModelGaloisDerivedComparison f j kbar Λ σ) ℤ :=
  Stacks.DerivedIndexing.natTransCommShift_rightDerivedFunctorPlusCompIsoOfIso_inv _ _ _ _

/-- The unit of `R(s̃_σ)_*` followed by `RΓ(C, -) ∘ R(s̃_σ)_* = RΓ(C, -)` is natural. -/
lemma geometricSmoothModelGaloisDerivedComparison_unit_naturality
    {Y Y' : EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb} (h : Y ⟶ Y') :
    (etaleModuleGlobalSections.{u, 0} Λ
        (geometricSmoothModel f j kbar).Vb).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor
        (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).map
        ((etaleModuleDirectImage.{u, 0} Λ (geometricSmoothModelGaloisAut f j kbar σ)).map h)) ≫
        ((etaleModuleGlobalSections.{u, 0} Λ
            (geometricSmoothModel f j kbar).Vb).rightDerivedFunctorPlus.map
            ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle (etaleModuleDirectImage.{u, 0} Λ
            (geometricSmoothModelGaloisAut f j kbar σ))).app Y') ≫
            (geometricSmoothModelGaloisDerivedComparison f j kbar Λ σ).app
            ((DerivedCategory.Plus.singleFunctor
            (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).obj Y')) =
      ((etaleModuleGlobalSections.{u, 0} Λ
          (geometricSmoothModel f j kbar).Vb).rightDerivedFunctorPlus.map
          ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle (etaleModuleDirectImage.{u, 0} Λ
          (geometricSmoothModelGaloisAut f j kbar σ))).app Y) ≫
          (geometricSmoothModelGaloisDerivedComparison f j kbar Λ σ).app
          ((DerivedCategory.Plus.singleFunctor
          (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).obj Y)) ≫
        (etaleModuleGlobalSections.{u, 0} Λ
            (geometricSmoothModel f j kbar).Vb).rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor
            (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).map h) := by
  have h1 : (DerivedCategory.Plus.singleFunctor
      (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).map
      ((etaleModuleDirectImage.{u, 0} Λ (geometricSmoothModelGaloisAut f j kbar σ)).map h) ≫
      (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle (etaleModuleDirectImage.{u, 0} Λ
      (geometricSmoothModelGaloisAut f j kbar σ))).app Y' =
      (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle (etaleModuleDirectImage.{u, 0} Λ
          (geometricSmoothModelGaloisAut f j kbar σ))).app Y ≫
          (etaleModuleDirectImage.{u, 0} Λ
          (geometricSmoothModelGaloisAut f j kbar σ)).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor
          (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).map h) :=
    (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle (etaleModuleDirectImage.{u, 0} Λ
        (geometricSmoothModelGaloisAut f j kbar σ))).naturality h
  have h2 : (etaleModuleGlobalSections.{u, 0} Λ
      (geometricSmoothModel f j kbar).Vb).rightDerivedFunctorPlus.map
      ((etaleModuleDirectImage.{u, 0} Λ
      (geometricSmoothModelGaloisAut f j kbar σ)).rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.singleFunctor
      (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).map h)) ≫
      (geometricSmoothModelGaloisDerivedComparison f j kbar Λ σ).app
          ((DerivedCategory.Plus.singleFunctor
          (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).obj Y') =
          (geometricSmoothModelGaloisDerivedComparison f j kbar Λ σ).app
          ((DerivedCategory.Plus.singleFunctor
          (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).obj Y) ≫
          (etaleModuleGlobalSections.{u, 0} Λ
          (geometricSmoothModel f j kbar).Vb).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor
          (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).map h) :=
    (geometricSmoothModelGaloisDerivedComparison f j kbar Λ σ).naturality
        ((DerivedCategory.Plus.singleFunctor
        (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).map h)
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, h1, CategoryTheory.Functor.map_comp,
    Category.assoc]
  exact (congrArg (_ ≫ ·) h2).trans (Category.assoc _ _ _).symm

/-- `H^i(C, (s̃_σ)_* -) ≅ H^i(C, -)` is the unit of `R(s̃_σ)_*` followed by
`RΓ(C, -) ∘ R(s̃_σ)_* = RΓ(C, -)`. -/
lemma integralDirectImageCohomologyIso_hom_geometricSmoothModelGaloisAut
    (N : EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) (i : ℤ) :
    (integralDirectImageCohomologyIso Λ (geometricSmoothModelGaloisAut f j kbar σ) N i).hom =
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
          ((etaleModuleGlobalSections.{u, 0} Λ
          (geometricSmoothModel f j kbar).Vb).rightDerivedFunctorPlus.map
          ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle (etaleModuleDirectImage.{u, 0} Λ
          (geometricSmoothModelGaloisAut f j kbar σ))).app N) ≫
          (geometricSmoothModelGaloisDerivedComparison f j kbar Λ σ).app
          ((DerivedCategory.Plus.singleFunctor
          (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).obj N)) := by
  have hu := Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso_hom
      (etaleModuleDirectImage.{u, 0} Λ (geometricSmoothModelGaloisAut f j kbar σ))
  change (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
      ((etaleModuleGlobalSections.{u, 0} Λ
      (geometricSmoothModel f j kbar).Vb).rightDerivedFunctorPlus.map
      ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso (etaleModuleDirectImage.{u, 0} Λ
          (geometricSmoothModelGaloisAut f j kbar σ)) 0).hom.app N) ≫
      (geometricSmoothModelGaloisDerivedComparison f j kbar Λ σ).app
          ((DerivedCategory.Plus.singleFunctor
          (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).obj N)) = _
  exact congrArg (fun z ↦ (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
      ((etaleModuleGlobalSections.{u, 0} Λ
      (geometricSmoothModel f j kbar).Vb).rightDerivedFunctorPlus.map (z.app N) ≫
    (geometricSmoothModelGaloisDerivedComparison f j kbar Λ σ).app
        ((DerivedCategory.Plus.singleFunctor
        (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).obj N))) hu

/-- The pullback action of `s̃_σ` on the smooth model, unfolded. -/
lemma geometricSmoothModelGaloisAction_eq_homologyFunctor (F : EtaleModules.{u, 0} Λ X) (i : ℤ) :
    geometricSmoothModelGaloisAction f j kbar Λ σ F i =
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
          ((etaleModuleGlobalSections.{u, 0} Λ
          (geometricSmoothModel f j kbar).Vb).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor
          (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).map
          (geometricSmoothModelInverseImageIso f j kbar Λ F).inv)) ≫
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
            ((etaleModuleGlobalSections.{u, 0} Λ
            (geometricSmoothModel f j kbar).Vb).rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor
            (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).map ((selfMapTwist.{u, 0}
            Λ (geometricSmoothModelProj f j kbar) (geometricSmoothModelGaloisAut f j kbar σ)
            (geometricSmoothModelGaloisAut_comp_proj f j kbar σ)).app
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)))) ≫
          (integralDirectImageCohomologyIso Λ (geometricSmoothModelGaloisAut f j kbar σ)
              ((etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).obj
              ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) i).hom) ≫
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
            ((etaleModuleGlobalSections.{u, 0} Λ
            (geometricSmoothModel f j kbar).Vb).rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor
            (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).map
            (geometricSmoothModelInverseImageIso f j kbar Λ F).hom)) :=
  rfl

/-- The map attached to the Galois twist, unfolded. -/
lemma derivedPairMap_geometricSmoothModelGaloisTwistApp_eq (F : EtaleModules.{u, 0} Λ X) :
    Stacks.DerivedIndexing.derivedPairMap (etaleModuleDirectImage.{u, 0} Λ
        (geometricSmoothModelGaloisAut f j kbar σ)) (etaleModuleGlobalSections.{u, 0} Λ
        (geometricSmoothModel f j kbar).Vb) (etaleModuleGlobalSections.{u, 0} Λ
        (geometricSmoothModel f j kbar).Vb)
        (geometricSmoothModelGaloisDerivedComparison f j kbar Λ σ)
        (geometricSmoothModelGaloisTwistApp f j kbar Λ σ F) =
      (etaleModuleGlobalSections.{u, 0} Λ
          (geometricSmoothModel f j kbar).Vb).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor
          (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).map
          (geometricSmoothModelInverseImageIso f j kbar Λ F).inv) ≫
        (etaleModuleGlobalSections.{u, 0} Λ
            (geometricSmoothModel f j kbar).Vb).rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor
            (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).map ((selfMapTwist.{u, 0}
            Λ (geometricSmoothModelProj f j kbar) (geometricSmoothModelGaloisAut f j kbar σ)
            (geometricSmoothModelGaloisAut_comp_proj f j kbar σ)).app
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))) ≫
        (etaleModuleGlobalSections.{u, 0} Λ
            (geometricSmoothModel f j kbar).Vb).rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor
            (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).map
            ((etaleModuleDirectImage.{u, 0} Λ (geometricSmoothModelGaloisAut f j kbar σ)).map
            (geometricSmoothModelInverseImageIso f j kbar Λ F).hom)) ≫
        ((etaleModuleGlobalSections.{u, 0} Λ
            (geometricSmoothModel f j kbar).Vb).rightDerivedFunctorPlus.map
            ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle (etaleModuleDirectImage.{u, 0} Λ
            (geometricSmoothModelGaloisAut f j kbar σ))).app ((etaleModuleExtensionByZero.{u, 0} Λ
            (geometricSmoothModel f j kbar).j).obj ((etaleModuleInverseImage.{u, 0} Λ
            (pullback.fst f (specAlgebraMap k kbar))).obj F))) ≫
            (geometricSmoothModelGaloisDerivedComparison f j kbar Λ σ).app
            ((DerivedCategory.Plus.singleFunctor
            (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).obj
            ((etaleModuleInverseImage.{u, 0} Λ
            (pullback.fst f (specAlgebraMap k kbar))).obj F)))) := by
  dsimp only [Stacks.DerivedIndexing.derivedPairMap, geometricSmoothModelGaloisTwistApp]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]

/-- The map attached to the Galois twist factors through `q^{-1}(j_! F) ≅ j_{C!}(F|_{X_k̄})`: it
is the twist of `q^{-1}(j_! F)` followed by the unit of `R(s̃_σ)_*` and
`RΓ(C, -) ∘ R(s̃_σ)_* = RΓ(C, -)`, conjugated by that isomorphism. -/
lemma derivedPairMap_geometricSmoothModelGaloisTwistApp_eq_comp (F : EtaleModules.{u, 0} Λ X) :
    Stacks.DerivedIndexing.derivedPairMap (etaleModuleDirectImage.{u, 0} Λ
        (geometricSmoothModelGaloisAut f j kbar σ)) (etaleModuleGlobalSections.{u, 0} Λ
        (geometricSmoothModel f j kbar).Vb) (etaleModuleGlobalSections.{u, 0} Λ
        (geometricSmoothModel f j kbar).Vb)
        (geometricSmoothModelGaloisDerivedComparison f j kbar Λ σ)
        (geometricSmoothModelGaloisTwistApp f j kbar Λ σ F) =
      (etaleModuleGlobalSections.{u, 0} Λ
          (geometricSmoothModel f j kbar).Vb).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor
          (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).map
          (geometricSmoothModelInverseImageIso f j kbar Λ F).inv) ≫
        ((etaleModuleGlobalSections.{u, 0} Λ
            (geometricSmoothModel f j kbar).Vb).rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor
            (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).map ((selfMapTwist.{u, 0}
            Λ (geometricSmoothModelProj f j kbar) (geometricSmoothModelGaloisAut f j kbar σ)
            (geometricSmoothModelGaloisAut_comp_proj f j kbar σ)).app
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))) ≫
          ((etaleModuleGlobalSections.{u, 0} Λ
              (geometricSmoothModel f j kbar).Vb).rightDerivedFunctorPlus.map
              ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle (etaleModuleDirectImage.{u, 0} Λ
              (geometricSmoothModelGaloisAut f j kbar σ))).app ((etaleModuleInverseImage.{u, 0} Λ
              (geometricSmoothModelProj f j kbar)).obj
              ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))) ≫
              (geometricSmoothModelGaloisDerivedComparison f j kbar Λ σ).app
              ((DerivedCategory.Plus.singleFunctor
              (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).obj
              ((etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).obj
              ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))))) ≫
        (etaleModuleGlobalSections.{u, 0} Λ
            (geometricSmoothModel f j kbar).Vb).rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor
            (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).map
            (geometricSmoothModelInverseImageIso f j kbar Λ F).hom) := by
  refine (derivedPairMap_geometricSmoothModelGaloisTwistApp_eq f j kbar Λ σ F).trans ?_
  simp only [Category.assoc]
  exact congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (by
    simpa only [Category.assoc] using
      geometricSmoothModelGaloisDerivedComparison_unit_naturality f j kbar Λ σ
          (geometricSmoothModelInverseImageIso f j kbar Λ F).hom))

/-- In degree `i`, the composite of `q^{-1}(j_! F) ≅ j_{C!}(F|_{X_k̄})`, the twist, the unit of
`R(s̃_σ)_*` and `RΓ(C, -) ∘ R(s̃_σ)_* = RΓ(C, -)` is the pullback action of `s̃_σ`
(`Stacks.EtaleCohomology.geometricSmoothModelGaloisAction`). -/
lemma geometricSmoothModelGaloisAction_eq_homologyFunctor_comp (F : EtaleModules.{u, 0} Λ X)
    (i : ℤ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
        ((etaleModuleGlobalSections.{u, 0} Λ
        (geometricSmoothModel f j kbar).Vb).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor
        (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).map
        (geometricSmoothModelInverseImageIso f j kbar Λ F).inv) ≫
        ((etaleModuleGlobalSections.{u, 0} Λ
            (geometricSmoothModel f j kbar).Vb).rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor
            (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).map ((selfMapTwist.{u, 0}
            Λ (geometricSmoothModelProj f j kbar) (geometricSmoothModelGaloisAut f j kbar σ)
            (geometricSmoothModelGaloisAut_comp_proj f j kbar σ)).app
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))) ≫
          ((etaleModuleGlobalSections.{u, 0} Λ
              (geometricSmoothModel f j kbar).Vb).rightDerivedFunctorPlus.map
              ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle (etaleModuleDirectImage.{u, 0} Λ
              (geometricSmoothModelGaloisAut f j kbar σ))).app ((etaleModuleInverseImage.{u, 0} Λ
              (geometricSmoothModelProj f j kbar)).obj
              ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))) ≫
              (geometricSmoothModelGaloisDerivedComparison f j kbar Λ σ).app
              ((DerivedCategory.Plus.singleFunctor
              (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).obj
              ((etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).obj
              ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))))) ≫
        (etaleModuleGlobalSections.{u, 0} Λ
            (geometricSmoothModel f j kbar).Vb).rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor
            (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).map
            (geometricSmoothModelInverseImageIso f j kbar Λ F).hom)) =
      geometricSmoothModelGaloisAction f j kbar Λ σ F i := by
  refine Eq.trans ?_ (geometricSmoothModelGaloisAction_eq_homologyFunctor f j kbar Λ σ F i).symm
  refine Eq.trans ?_ (congrArg (fun z ↦ (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ)
      i).map ((etaleModuleGlobalSections.{u, 0} Λ
      (geometricSmoothModel f j kbar).Vb).rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.singleFunctor
          (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).map
          (geometricSmoothModelInverseImageIso f j kbar Λ F).inv)) ≫
          ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
          ((etaleModuleGlobalSections.{u, 0} Λ
          (geometricSmoothModel f j kbar).Vb).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor
          (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).map ((selfMapTwist.{u, 0} Λ
          (geometricSmoothModelProj f j kbar) (geometricSmoothModelGaloisAut f j kbar σ)
          (geometricSmoothModelGaloisAut_comp_proj f j kbar σ)).app
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)))) ≫ z) ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
          ((etaleModuleGlobalSections.{u, 0} Λ
          (geometricSmoothModel f j kbar).Vb).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor
          (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 0).map
          (geometricSmoothModelInverseImageIso f j kbar Λ F).hom)))
    (integralDirectImageCohomologyIso_hom_geometricSmoothModelGaloisAut f j kbar Λ σ
        ((etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) i).symm)
  exact ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map_comp _ _).trans
      (congrArg (_ ≫ ·) ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ)
      i).map_comp _ _)) |>.trans
    (congrArg (fun z ↦ _ ≫ z ≫ _) ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ)
        i).map_comp _ _)) |>.trans (by simp only [Category.assoc])

/-- **The endomorphism of `H^i(C, j_{C!}(F|_{X_k̄}))` attached to the Galois twist is the pullback
action of `s̃_σ`** (`Stacks.EtaleCohomology.geometricSmoothModelGaloisAction`). -/
theorem homologyFunctor_map_derivedPairMap_geometricSmoothModelGaloisTwistApp
    (F : EtaleModules.{u, 0} Λ X) (i : ℤ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
        (Stacks.DerivedIndexing.derivedPairMap (etaleModuleDirectImage.{u, 0} Λ
        (geometricSmoothModelGaloisAut f j kbar σ)) (etaleModuleGlobalSections.{u, 0} Λ
        (geometricSmoothModel f j kbar).Vb) (etaleModuleGlobalSections.{u, 0} Λ
        (geometricSmoothModel f j kbar).Vb)
        (geometricSmoothModelGaloisDerivedComparison f j kbar Λ σ)
        (geometricSmoothModelGaloisTwistApp f j kbar Λ σ F)) =
      geometricSmoothModelGaloisAction f j kbar Λ σ F i :=
  (congrArg (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
      (derivedPairMap_geometricSmoothModelGaloisTwistApp_eq_comp f j kbar Λ σ F)).trans
    (geometricSmoothModelGaloisAction_eq_homologyFunctor_comp f j kbar Λ σ F i)

end Derived

end Twist

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

open Stacks.GroupCohomology Stacks.EtaleCohomology

attribute [local instance high] etaleModules_hasSheafify

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1]
  (x : GeometricPoint X.1) (Λ : Type) [Ring Λ] [Finite Λ]
  {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
  [GeometricallyConnected f] (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] (σ : kbar ≃ₐ[k] kbar)

/-- **The Galois twist of `ρ ↦ j_{C!}(ℱ_ρ|_{X_k̄})`**
(`Stacks.EtaleCohomology.geometricSmoothModelGaloisTwistApp` at `ℱ_ρ`), natural in `ρ`. -/
def compactSupportRepresentationGaloisTwist :
    compactSupportRepresentationSheaf B X x Λ f j kbar ⟶
      compactSupportRepresentationSheaf B X x Λ f j kbar ⋙
        etaleModuleDirectImage.{u, 0} Λ (geometricSmoothModelGaloisAut f j kbar σ) where
  app ρ := geometricSmoothModelGaloisTwistApp f j kbar Λ σ ((representationSheaf B X x Λ).obj ρ)
  naturality _ _ v := geometricSmoothModelGaloisTwistApp_naturality f j kbar Λ σ
    ((representationSheaf B X x Λ).map v)

section Action

attribute [local instance] HasDerivedCategory.standard Functor.commShiftRightDerivedFunctorPlus

/-- Enough injectives for sheaves of `Λ`-modules at coefficient universe `0`, pinned. -/
local instance (priority := 3000) etaleModulesEnoughInjectivesGaloisDeltaRep (Λ : Type) [Ring Λ]
    (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

/-- **The action of `σ ∈ Aut_k(k̄)` on `ρ ↦ H^q(C, j_{C!}(ℱ_ρ|_{X_k̄})) = H^q_c(X_k̄, ℱ_ρ)` as an
endomorphism of cohomological δ-functors**: it commutes with the connecting morphisms. -/
def compactSupportRepresentationCohomologyGalois :
    compactSupportRepresentationCohomology B X x Λ f j kbar ⟶
      compactSupportRepresentationCohomology B X x Λ f j kbar :=
  have := preservesFiniteLimits_compactSupportRepresentationSheaf B X x Λ f j kbar
  have := preservesFiniteColimits_compactSupportRepresentationSheaf B X x Λ f j kbar
  Stacks.DerivedIndexing.twistDeltaHom
    (etaleModuleDirectImage.{u, 0} Λ (geometricSmoothModelGaloisAut f j kbar σ))
    (etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb)
    (geometricSmoothModelGaloisDerivedComparison f j kbar Λ σ)
    (compactSupportRepresentationSheaf B X x Λ f j kbar)
    (compactSupportRepresentationGaloisTwist B X x Λ f j kbar σ)

/-- **In degree `q` the action of `σ` is the pullback action of `s̃_σ` on the smooth model**,
read through the two indexings of the right derived functors. -/
theorem compactSupportRepresentationCohomologyGalois_app_app (q : ℕ)
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    ((compactSupportRepresentationCohomologyGalois B X x Λ f j kbar σ).app q).app ρ =
      (Stacks.DerivedIndexing.rightDerivedIso
          (etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) q).hom.app
          ((compactSupportRepresentationSheaf B X x Λ f j kbar).obj ρ) ≫
        geometricSmoothModelGaloisAction f j kbar Λ σ ((representationSheaf B X x Λ).obj ρ) q ≫
        (Stacks.DerivedIndexing.rightDerivedIso
          (etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) q).inv.app
          ((compactSupportRepresentationSheaf B X x Λ f j kbar).obj ρ) :=
  congrArg (fun z ↦ (Stacks.DerivedIndexing.rightDerivedIso
      (etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) q).hom.app
        ((compactSupportRepresentationSheaf B X x Λ f j kbar).obj ρ) ≫ z ≫
      (Stacks.DerivedIndexing.rightDerivedIso
        (etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) q).inv.app
        ((compactSupportRepresentationSheaf B X x Λ f j kbar).obj ρ))
    (homologyFunctor_map_derivedPairMap_geometricSmoothModelGaloisTwistApp f j kbar Λ σ
      ((representationSheaf B X x Λ).obj ρ) q)

end Action

end AlgebraicGeometry

end

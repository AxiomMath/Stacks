module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffinePointwiseLocalModel

/-!
# Stacks 0DJ8 (1) ⟹ (2) over a pushout square of rings

Let `R → A`, `R → R'`, `A → A'`, `R' → A'` be a pushout square of rings, `M` a complex of
`A`-modules, `N` a complex of `A'`-modules and `ψ₀ : A' ⊗_A M ⟶ N`.  Suppose that for every prime
`q` of `A'`, with images `p'`, `p` in `R'`, `R`, and `𝔮` in `A`, the map of Stacks 0DJ7 of the
square of localizations `R_p → A_𝔮 → A'_q ← R'_{p'}` at the localization of `ψ₀` is invertible in
every degree.  Then for a quasi-isomorphism `π : P ⟶ M` from a K-flat complex of `R`-modules the
map of complexes `R' ⊗_R P ⟶ N`, `1 ⊗ x ↦ ψ₀(1 ⊗ π x)`, is a quasi-isomorphism.  This is the
algebraic content of (1) ⟹ (2) of Stacks 0DJ8, through Algebra, Lemma 00HN.

## Main results

* `RingTheory.TorIndependence.bijective_localizedModule_map_of_isIso_local`
* `RingTheory.TorIndependence.quasiIso_of_bijective_localizedModule_map`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct ChangeOfRings
open CochainComplex.DerivedExtensionScalars

universe u

namespace RingTheory.TorIndependence

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R A R' A' R₀ : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [CommRing R₀]
  [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']
  [Algebra R R₀] [Algebra R₀ R'] [IsScalarTower R R₀ R'] [Module.Flat R R₀]

local notation "B₀" => A ⊗[R] R₀

/-- **The localization at a prime from a localized square.** -/
theorem bijective_localizedModule_map_of_isIso_local
    (hsurj : Function.Surjective (algebraMap R₀ R'))
    (hpush : Function.Bijective (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')))
    {F : CochainComplex (ModuleCat.{u} R₀) ℤ}
    (ε : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R₀) 0).obj (ModuleCat.of R₀ R'))
    (hF : F.KFlat) [QuasiIso ε]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (N : CochainComplex (ModuleCat.{u} A') ℤ)
    (ψ₀ : ((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M ⟶ N)
    (q : Ideal A') [q.IsPrime]
    (B R₁ A₁ R'₁ : Type u) [CommRing B] [CommRing R₁] [CommRing A₁] [CommRing R'₁]
    [Algebra A' B] [Algebra A B] [Algebra R B] [Algebra R' B] [IsScalarTower A A' B]
    [IsScalarTower R' A' B] [IsScalarTower R A B] [IsScalarTower R R' B]
    [IsLocalization.AtPrime B q]
    [Algebra R₁ A₁] [Algebra R₁ R'₁] [Algebra R₁ B] [Algebra A₁ B] [Algebra R'₁ B]
    [IsScalarTower R₁ A₁ B] [IsScalarTower R₁ R'₁ B]
    [Algebra R R₁] [Algebra A A₁] [Algebra R' R'₁] [Algebra R A₁] [Algebra R R'₁]
    [IsScalarTower R A A₁] [IsScalarTower R R₁ A₁] [IsScalarTower A A₁ B] [IsScalarTower R' R'₁ B]
    [IsScalarTower R R₁ R'₁] [IsScalarTower R R' R'₁]
    (U : Submonoid R) [IsLocalization U R₁] (W : Submonoid A) [IsLocalization W A₁]
    (V : Submonoid R') [IsLocalization V R'₁]
    (hloc₁ : letI := (baseChangeTensorRingMap (R := R₁) (A := A₁) (R' := R'₁) (A' := B)).toAlgebra
      ∃ S : Submonoid (A₁ ⊗[R₁] R'₁), IsLocalization S B)
    {M₁ : CochainComplex (ModuleCat.{u} A₁) ℤ}
    (eM : ((baseChangeFunctor A A₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj M ≅ M₁)
    {Z : CochainComplex (ModuleCat.{u} B) ℤ}
    (ζ : N ⟶ ((ModuleCat.restrictScalars (algebraMap A' B)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj Z)
    (hζ : ∀ i, IsLocalizedModule q.primeCompl (ζ.f i).hom)
    (α : ((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M ⟶ Z)
    (hα : ∀ i (m : M.X i), (α.f i).hom ((1 : B) ⊗ₜ[A,algebraMap A B] m) =
      (ζ.f i).hom ((ψ₀.f i).hom ((1 : A') ⊗ₜ[A,algebraMap A A'] m)))
    (α₁ : ((ModuleCat.extendScalars (algebraMap A₁ B)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M₁ ⟶ Z)
    (hα₁ : ∀ i (m : M.X i), (α₁.f i).hom ((1 : B) ⊗ₜ[A₁,algebraMap A₁ B]
      (eM.hom.f i).hom ((1 : A₁) ⊗ₜ[A] m)) = (α.f i).hom ((1 : B) ⊗ₜ[A,algebraMap A B] m))
    (n : ℤ)
    (hiso : IsIso (ringBaseChangeCohomologyMap (R := R₁) (R' := R'₁) (DerivedCategory.Q.obj M₁)
      (DerivedCategory.Q.obj Z) (alphaH A₁ B M₁ ≫ DerivedCategory.Q.map α₁) n)) :
    Function.Bijective (LocalizedModule.map (q.comap (modelRingMap R A R' A' R₀)).primeCompl
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n).map
        (DerivedCategory.Q.map (modelKappa (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀)
          ε M N ψ₀))).hom) :=
  bijective_localizedModule_map_of_isLocalizedModule (R := R) (A := A) (R' := R') (A' := A')
    (R₀ := R₀) ε hF n q B hsurj hpush M N ψ₀ Z ζ hζ α hα
    ((isIso_local_iff_isLocalizedModule_modelKappa U W V hsurj ε hF hloc₁ eM α α₁ hα₁ n).1 hiso)

/-- **(1) ⟹ (2) of Stacks 0DJ8 over a pushout square of rings, through its localizations.** -/
theorem quasiIso_of_bijective_localizedModule_map
    (hsurj : Function.Surjective (algebraMap R₀ R'))
    (hpush : Function.Bijective (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')))
    {F : CochainComplex (ModuleCat.{u} R₀) ℤ}
    (ε : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R₀) 0).obj (ModuleCat.of R₀ R'))
    (hF : F.KFlat) [QuasiIso ε]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (N : CochainComplex (ModuleCat.{u} A') ℤ)
    (ψ₀ : ((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M ⟶ N)
    (h : ∀ (n : ℤ) (q : Ideal A') [q.IsPrime], Function.Bijective
      (LocalizedModule.map (q.comap (modelRingMap R A R' A' R₀)).primeCompl
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n).map
          (DerivedCategory.Q.map (modelKappa (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀)
            ε M N ψ₀))).hom))
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat)
    (π : P ⟶ ((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M) [QuasiIso π]
    (κ₀ : ((ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P ⟶
      ((ModuleCat.restrictScalars (algebraMap R' A')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N)
    (hκ : ∀ n (x : P.X n), (κ₀.f n).hom ((1 : R') ⊗ₜ[R,algebraMap R R'] x) =
      (ψ₀.f n).hom ((1 : A') ⊗ₜ[A,algebraMap A A'] (show M.X n from (π.f n).hom x))) :
    QuasiIso κ₀ :=
  quasiIso_of_bijective_cohomologyComparisonMap M N ψ₀ P hP π κ₀ hκ fun n =>
    bijective_cohomologyComparisonMap_of_localizations ε hF n hsurj hpush M N ψ₀
      fun q _ => h n q

end RingTheory.TorIndependence

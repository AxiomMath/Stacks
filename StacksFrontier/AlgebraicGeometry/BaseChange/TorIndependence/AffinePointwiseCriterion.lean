module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.ModelHomology
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.RingCriterion
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.LocalizedModuleCriterion
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.StalkLocalizationCriterion
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffinePointwiseLocalization
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.RingTensor
import all StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.LocalizedModuleCriterion

/-!
# A quasi-isomorphism criterion over a square of rings, through cohomology

Let `R → A`, `R → R'`, `A → A'`, `R' → A'` be a commutative square of rings, `M` a complex of
`A`-modules, `N` a complex of `A'`-modules and `ψ₀ : A' ⊗_A M ⟶ N` a map of complexes.  For a
quasi-isomorphism `π : P ⟶ M` from a K-flat complex of `R`-modules, the map of complexes
`R' ⊗_R P ⟶ N`, `1 ⊗ x ↦ ψ₀(1 ⊗ π x)`, computes the composition
`M ⊗^L_R R' ⟶ M ⊗^L_A A' ⟶ N`; it is a quasi-isomorphism as soon as the comparison
`cohomologyComparisonMap` followed by `ψ₀` is bijective on cohomology in every degree.

## Main results

* `RingTheory.TorIndependence.quasiIso_of_bijective_cohomologyComparisonMap`: the map of
  complexes `R' ⊗_R P ⟶ N` is a quasi-isomorphism when the comparison followed by `ψ₀` is
  bijective in every degree.
* `RingTheory.TorIndependence.bijective_cohomologyComparisonMap_of_localizations`: for a pushout
  square, the comparison followed by `α` is bijective once the cohomology of the model map is
  bijective after localization at the preimage of every prime of `A'`.
* `RingTheory.TorIndependence.bijective_localizedModule_map_of_isLocalizedModule`: the model map
  localizes to a bijection at the preimage of a prime `q` of `A'` when the model map of the
  square with `A'` replaced by its localization at `q` is a localization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
open CochainComplex.DerivedExtensionScalars

universe u

namespace RingTheory.TorIndependence

attribute [local instance 10000] HasDerivedCategory.standard

variable {R A R' A' : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']

/-- The map of complexes `R' ⊗_R P ⟶ N` with `1 ⊗ x ↦ ψ₀(1 ⊗ π x)` is the termwise
comparison of the square composed with `ψ₀`. -/
theorem eq_extendScalars_comp_tau0C (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (N : CochainComplex (ModuleCat.{u} A') ℤ)
    (ψ₀ : ((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M ⟶ N)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (π : P ⟶ ((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M)
    (κ₀ : ((ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P ⟶
      ((ModuleCat.restrictScalars (algebraMap R' A')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N)
    (hκ : ∀ n (x : P.X n), (κ₀.f n).hom ((1 : R') ⊗ₜ[R,algebraMap R R'] x) =
      (ψ₀.f n).hom ((1 : A') ⊗ₜ[A,algebraMap A A'] (show M.X n from (π.f n).hom x))) :
    κ₀ = ((ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ)).map π ≫ tau0C R A R' A' M ≫
      ((ModuleCat.restrictScalars (algebraMap R' A')).mapHomologicalComplex
        (ComplexShape.up ℤ)).map ψ₀ := by
  ext n : 1
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  refine (hκ n x).trans ?_
  show _ = (ψ₀.f n).hom (((squareTermComparison R A R' A').app (M.X n)).hom
    ((1 : R') ⊗ₜ[R, algebraMap R R'] (π.f n).hom x))
  rw [squareTermComparison_tmul, map_one]

/-- If the comparison `cohomologyComparisonMap` followed by `ψ₀` is bijective in every degree,
the map of complexes `R' ⊗_R P ⟶ N`, `1 ⊗ x ↦ ψ₀(1 ⊗ π x)`, is a quasi-isomorphism. -/
theorem quasiIso_of_bijective_cohomologyComparisonMap (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (N : CochainComplex (ModuleCat.{u} A') ℤ)
    (ψ₀ : ((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M ⟶ N)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat)
    (π : P ⟶ ((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M) [QuasiIso π]
    (κ₀ : ((ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P ⟶
      ((ModuleCat.restrictScalars (algebraMap R' A')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N)
    (hκ : ∀ n (x : P.X n), (κ₀.f n).hom ((1 : R') ⊗ₜ[R,algebraMap R R'] x) =
      (ψ₀.f n).hom ((1 : A') ⊗ₜ[A,algebraMap A A'] (show M.X n from (π.f n).hom x)))
    (h : ∀ n, Function.Bijective (cohomologyComparisonMap (R := R) (R' := R')
      (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj N)
      (alphaH A A' M ≫ DerivedCategory.Q.map ψ₀) n).hom) :
    QuasiIso κ₀ := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso, DerivedCategory.isIso_iff]
  intro n
  let Tg := (totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).functor
  let C := (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory
  let J := DerivedCategory.homologyFunctor (ModuleCat.{u} R') n
  let fM : (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj
      (DerivedCategory.Q.obj M) ≅ DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) :=
    (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategoryFactors.app M
  let fN : C.obj (DerivedCategory.Q.obj N) ≅ DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars (algebraMap R' A')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N) :=
    (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategoryFactors.app N
  let fN' : C.obj (DerivedCategory.Q.obj
      (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M)) ≅ DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars (algebraMap R' A')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
          (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M)) :=
    (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategoryFactors.app
      (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M)
  let τ : Tg.obj ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj
      (DerivedCategory.Q.obj M)) ⟶ C.obj ((totalDerivedExtensionScalars.{u, u, u}
        (algebraMap A A')).functor.obj (DerivedCategory.Q.obj M)) :=
    (squareDerivedComparison (R := R) (A := A) (R' := R') (A' := A')).app
      (DerivedCategory.Q.obj M)
  have hsq : τ ≫ C.map (alphaH A A' M) = Tg.map fM.hom ≫
      alphaG R R' (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M) ≫ DerivedCategory.Q.map (tau0C R A R' A' M) ≫ fN'.inv :=
    squareDerivedComparison_app_Q'' (R := R) (A := A) (R' := R') (A' := A') M
  have e1 : Tg.map fM.inv ≫ τ ≫ C.map (alphaH A A' M) =
      alphaG R R' (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M) ≫ DerivedCategory.Q.map (tau0C R A R' A' M) ≫ fN'.inv := by
    rw [hsq, ← Tg.map_comp_assoc, Iso.inv_hom_id, Tg.map_id, Category.id_comp]
  have hnat : fN'.inv ≫ C.map (DerivedCategory.Q.map ψ₀) =
      DerivedCategory.Q.map (((ModuleCat.restrictScalars (algebraMap R' A')).mapHomologicalComplex
        (ComplexShape.up ℤ)).map ψ₀) ≫ fN.inv :=
    ((ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategoryFactors.inv.naturality
      ψ₀).symm
  have hG : Tg.map (DerivedCategory.Q.map π) ≫
      alphaG R R' (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M) =
      alphaG R R' P ≫ DerivedCategory.Q.map
        (((ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.up ℤ)).map π) :=
    ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).comparison).naturality π
  have E : Tg.map (DerivedCategory.Q.map π) ≫ Tg.map fM.inv ≫ τ ≫
      C.map (alphaH A A' M ≫ DerivedCategory.Q.map ψ₀) =
      alphaG R R' P ≫ DerivedCategory.Q.map κ₀ ≫ fN.inv := by
    rw [C.map_comp, reassoc_of% e1, hnat, reassoc_of% hG,
      eq_extendScalars_comp_tau0C M N ψ₀ P π κ₀ hκ]
    simp only [Functor.map_comp, Category.assoc]
  have hπ : IsIso (Tg.map (DerivedCategory.Q.map π)) := inferInstance
  have hα : IsIso (alphaG R R' P) :=
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).comparison_isIso_of_kFlat P hP
  have hc : IsIso (J.map (τ ≫ C.map (alphaH A A' M ≫ DerivedCategory.Q.map ψ₀)) ≫
      ((ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategoryHomologyIso n).hom.app
        (DerivedCategory.Q.obj N)) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (h n)
  have hc' : IsIso (J.map (τ ≫ C.map (alphaH A A' M ≫ DerivedCategory.Q.map ψ₀))) :=
    IsIso.of_isIso_comp_right _
      (((ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategoryHomologyIso n).hom.app
        (DerivedCategory.Q.obj N))
  have hL : IsIso (J.map (Tg.map (DerivedCategory.Q.map π) ≫ Tg.map fM.inv ≫ τ ≫
      C.map (alphaH A A' M ≫ DerivedCategory.Q.map ψ₀))) := by
    rw [J.map_comp, J.map_comp]
    infer_instance
  rw [E, J.map_comp, J.map_comp] at hL
  have h1 : IsIso (J.map (DerivedCategory.Q.map κ₀) ≫ J.map fN.inv) :=
    IsIso.of_isIso_comp_left (J.map (alphaG R R' P)) _
  exact IsIso.of_isIso_comp_right (J.map (DerivedCategory.Q.map κ₀)) (J.map fN.inv)

/-- A module on which an element of a submonoid acts by zero has zero localization. -/
theorem subsingleton_localizedModule_of_smul_eq_zero {B : Type u} [CommRing B] (S : Submonoid B)
    {X : Type u} [AddCommGroup X] [Module B X] (k : B) (hk : k ∈ S) (h : ∀ x : X, k • x = 0) :
    Subsingleton (LocalizedModule S X) := by
  refine subsingleton_of_forall_eq 0 fun z => ?_
  induction z using LocalizedModule.induction_on with
  | h x s =>
    rw [← LocalizedModule.mk_cancel_common_left ⟨k, hk⟩ s x,
      show (⟨k, hk⟩ : S) • x = 0 from h x, LocalizedModule.zero_mk]

/-- A module linearly equivalent to one killed by an element of a submonoid has zero
localization. -/
private theorem subsingleton_localizedModule_of_equiv {B : Type u} [CommRing B] (S : Submonoid B)
    {X Y : Type u} [AddCommGroup X] [Module B X] [AddCommGroup Y] [Module B Y] (e : X ≃ₗ[B] Y)
    (k : B) (hk : k ∈ S) (h : ∀ y : Y, k • y = 0) : Subsingleton (LocalizedModule S X) :=
  subsingleton_localizedModule_of_smul_eq_zero S k hk fun x =>
    e.injective (by rw [map_smul, map_zero, h])

/-- A localization over a ring is one over any ring isomorphic to it. -/
theorem isLocalization_comap_of_bijective {C D B : Type u} [CommRing C] [CommRing D] [CommRing B]
    [Algebra D B] (k : C →+* D) (hk : Function.Bijective k) (S : Submonoid D)
    [IsLocalization S B] :
    letI := ((algebraMap D B).comp k).toAlgebra
    IsLocalization (S.comap k) B := by
  let e := RingEquiv.ofBijective k hk
  have h := IsLocalization.isLocalization_of_base_ringEquiv S B e.symm
  have hS : S.map e.symm = S.comap k := by
    ext x
    simp only [Submonoid.mem_map, Submonoid.mem_comap]
    refine ⟨?_, fun hx => ⟨k x, hx, e.symm_apply_apply x⟩⟩
    rintro ⟨y, hy, rfl⟩
    convert hy
    exact e.apply_symm_apply y
  rwa [hS] at h

/-- A map whose composite with a localization is a localization at the same submonoid is
bijective after localization. -/
theorem bijective_localizedModule_map_of_comp {B : Type u} [CommRing B] (S : Submonoid B)
    {X Y W : Type u} [AddCommGroup X] [Module B X] [AddCommGroup Y] [Module B Y]
    [AddCommGroup W] [Module B W] (F : X →ₗ[B] Y) (g : Y →ₗ[B] W) [hg : IsLocalizedModule S g]
    (hgF : IsLocalizedModule S (g ∘ₗ F)) :
    Function.Bijective (LocalizedModule.map S F) := by
  have hid : IsLocalizedModule.map S (g ∘ₗ F) g F = LinearMap.id :=
    IsLocalizedModule.linearMap_ext S (g ∘ₗ F) (g ∘ₗ F)
      ((IsLocalizedModule.map_comp S (g ∘ₗ F) g F).trans (LinearMap.id_comp _).symm)
  rw [Stacks.StalkLocalization.bijective_localizedModule_map_iff S F (g ∘ₗ F) g, hid]
  exact Function.bijective_id

section Global

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R₀ : Type u} [CommRing R₀] [Algebra R R₀] [Algebra R₀ R'] [IsScalarTower R R₀ R']

local notation "B₀" => A ⊗[R] R₀

variable {F : CochainComplex (ModuleCat.{u} R₀) ℤ}
  (ε : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R₀) 0).obj (ModuleCat.of R₀ R'))
  [Module.Flat R R₀] (hF : F.KFlat) [QuasiIso ε] (n : ℤ)

include hF in
/-- For a pushout square of rings, the comparison `cohomologyComparisonMap` followed by `α` is
bijective in degree `n` when the cohomology of the model map becomes bijective after
localization at the preimage of every prime of `A'`. -/
theorem bijective_cohomologyComparisonMap_of_localizations
    (hsurj : Function.Surjective (algebraMap R₀ R'))
    (hpush : Function.Bijective (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')))
    (N : CochainComplex (ModuleCat.{u} A) ℤ) (Z : CochainComplex (ModuleCat.{u} A') ℤ)
    (α : ((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N ⟶ Z)
    (h : ∀ (q : Ideal A') [q.IsPrime], Function.Bijective
      (LocalizedModule.map (q.comap (modelRingMap R A R' A' R₀)).primeCompl
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n).map
          (DerivedCategory.Q.map (modelKappa (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀)
            ε N Z α))).hom)) :
    Function.Bijective (cohomologyComparisonMap (R := R) (R' := R') (DerivedCategory.Q.obj N)
      (DerivedCategory.Q.obj Z) (alphaH A A' N ≫ DerivedCategory.Q.map α) n).hom := by
  set Hκ := ((DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n).map
    (DerivedCategory.Q.map (modelKappa (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀)
      ε N Z α))).hom with hHκ
  have hρ : Function.Surjective (modelRingMap R A R' A' R₀) :=
    hpush.2.comp (TensorProduct.map_surjective Function.surjective_id hsurj)
  have hκ : Function.Bijective Hκ := by
    rw [Stacks.StalkLocalization.bijective_iff_forall_bijective_localizedMap]
    intro P hP
    by_cases hker : RingHom.ker (modelRingMap R A R' A' R₀) ≤ P
    · have : (P.map (modelRingMap R A R' A' R₀)).IsPrime := Ideal.map_isPrime_of_surjective hρ hker
      have hq : (P.map (modelRingMap R A R' A' R₀)).comap (modelRingMap R A R' A' R₀) = P := by
        rw [Ideal.comap_map_of_surjective _ hρ, ← RingHom.ker_eq_comap_bot]
        exact sup_eq_left.2 hker
      have key : ∀ (Q : Ideal B₀) (hQ : Q.IsPrime), Q = P →
          Function.Bijective (LocalizedModule.map (@Ideal.primeCompl _ _ Q hQ) Hκ) →
            Function.Bijective (LocalizedModule.map P.primeCompl Hκ) := by
        rintro Q hQ rfl
        exact id
      exact key _ _ hq (h _)
    · obtain ⟨k, hk, hkP⟩ := Set.not_subset.1 hker
      have hk0 : modelRingMap R A R' A' R₀ k = 0 := hk
      have hk0' : modelBaseRingMap R A R' R₀ k = 0 := hpush.1 (hk0.trans (map_zero _).symm)
      have hsrc : Subsingleton (LocalizedModule P.primeCompl
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n).obj
            (DerivedCategory.Q.obj (modelComplex A F N)))) := by
        refine subsingleton_localizedModule_of_equiv _
          (modelHomologyLinearEquiv (R := R) (A := A) (R' := R') ε hF n N) k hkP fun y => ?_
        show (modelBaseRingMap R A R' R₀ k) • (show baseChangeCohomologyCat (R := R) (R' := R')
          (DerivedCategory.Q.obj N) n from y) = 0
        rw [hk0', zero_smul]
      have htgt : Subsingleton (LocalizedModule P.primeCompl
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n).obj
            (DerivedCategory.Q.obj
              (((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj Z)))) := by
        refine subsingleton_localizedModule_of_equiv _
          (modelTargetIso (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) n Z).toLinearEquiv
          k hkP fun y => ?_
        show (modelRingMap R A R' A' R₀ k) • (show (DerivedCategory.homologyFunctor
          (ModuleCat.{u} A') n).obj (DerivedCategory.Q.obj Z) from y) = 0
        rw [hk0, zero_smul]
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  have hcomp : (cohomologyComparisonMap (R := R) (R' := R') (DerivedCategory.Q.obj N)
      (DerivedCategory.Q.obj Z) (alphaH A A' N ≫ DerivedCategory.Q.map α) n).hom ∘
        (modelHomologyIso (R := R) ε hF n N).hom.hom =
      (modelTargetIso (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) n Z).hom.hom ∘ Hκ :=
    funext fun y => (modelKappa_homology_apply (R := R) (A := A) (R' := R') (A' := A')
      (R₀ := R₀) ε hF n N Z α y).symm
  have hE : Function.Bijective (modelHomologyIso (R := R) ε hF n N).hom.hom :=
    (modelHomologyIso (R := R) ε hF n N).toLinearEquiv.bijective
  refine (Function.Bijective.of_comp_iff _ hE).1 ((congrArg Function.Bijective hcomp).mpr ?_)
  exact (modelTargetIso (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) n
    Z).toLinearEquiv.bijective.comp hκ

section Local

variable (q : Ideal A') [q.IsPrime] (B : Type u) [CommRing B] [Algebra A' B] [Algebra A B]
  [Algebra R B] [Algebra R' B] [IsScalarTower A A' B] [IsScalarTower R' A' B]
  [IsScalarTower R A B] [IsScalarTower R R' B]

/-- For an `A'`-algebra `B`, the map `A ⊗_R R' → B` is the composite of `A ⊗_R R' → A'` with the
structure map `A' → B`. -/
theorem baseChangeTensorRingMap_comp_algebraMap :
    baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := B) =
      (algebraMap A' B).comp (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')) := by
  refine RingHom.ext fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add s t hs ht => rw [map_add, map_add, hs, ht]
  | tmul a r =>
    rw [baseChangeTensorRingMap_tmul, RingHom.comp_apply, baseChangeTensorRingMap_tmul, map_mul,
      ← IsScalarTower.algebraMap_apply A A' B, ← IsScalarTower.algebraMap_apply R' A' B]

omit [Module.Flat R R₀] in
/-- For an `A'`-algebra `B`, the map `A ⊗_R R₀ → B` sends `b` to the image under `A' → B` of the
image of `b` in `A'`. -/
theorem modelRingMap_apply_of_algebra (b : B₀) :
    modelRingMap R A R' B R₀ b = algebraMap A' B (modelRingMap R A R' A' R₀ b) := by
  show baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := B) _ = _
  rw [baseChangeTensorRingMap_comp_algebraMap (R := R) (A := A) (R' := R') (A' := A') B]
  rfl

/-- The map of complexes `ζ : Z ⟶ Z₁` from a complex of `A'`-modules to a complex of `B`-modules,
read over `A ⊗_R R₀` on both sides. -/
def modelTargetMap (Z : CochainComplex (ModuleCat.{u} A') ℤ)
    (Z₁ : CochainComplex (ModuleCat.{u} B) ℤ)
    (ζ : Z ⟶ ((ModuleCat.restrictScalars (algebraMap A' B)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj Z₁) :
    ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Z ⟶
      ((ModuleCat.restrictScalars (modelRingMap R A R' B R₀)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Z₁ where
  f i := ModuleCat.ofHom (X := (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).obj (Z.X i))
      (Y := (ModuleCat.restrictScalars (modelRingMap R A R' B R₀)).obj (Z₁.X i))
    { toFun := fun x => (ζ.f i).hom x
      map_add' := fun x y => (ζ.f i).hom.map_add x y
      map_smul' := fun b x =>
        ((ζ.f i).hom.map_smul (modelRingMap R A R' A' R₀ b) (show Z.X i from x)).trans
          (congrArg (fun c : B => c • (show Z₁.X i from (ζ.f i).hom x))
            (modelRingMap_apply_of_algebra (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀)
              B b).symm) }
  comm' i j _ := ModuleCat.hom_ext (LinearMap.ext fun x =>
    congrArg (fun φ => φ.hom x) (ζ.comm i j))

/-- The model map of the square through `B` is the model map of the square through `A'`
followed by `modelTargetMap ζ`, when `α₁` and `α` followed by `ζ` agree on the elements `1 ⊗ m`. -/
theorem modelKappa_algebra_eq (N : CochainComplex (ModuleCat.{u} A) ℤ)
    (Z : CochainComplex (ModuleCat.{u} A') ℤ)
    (α : ((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N ⟶ Z)
    (Z₁ : CochainComplex (ModuleCat.{u} B) ℤ)
    (ζ : Z ⟶ ((ModuleCat.restrictScalars (algebraMap A' B)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj Z₁)
    (α₁ : ((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N ⟶ Z₁)
    (hα : ∀ i (m : N.X i), (α₁.f i).hom ((1 : B) ⊗ₜ[A,algebraMap A B] m) =
      (ζ.f i).hom ((α.f i).hom ((1 : A') ⊗ₜ[A,algebraMap A A'] m))) :
    modelKappa (R := R) (A := A) (R' := R') (A' := B) (R₀ := R₀) ε N Z₁ α₁ =
      modelKappa (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) ε N Z α ≫
        modelTargetMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) B Z Z₁ ζ := by
  have key : ∀ i, (tau0C R A R' B N).f i ≫
      (ModuleCat.restrictScalars (algebraMap R' B)).map (α₁.f i) =
      (tau0C R A R' A' N).f i ≫ (ModuleCat.restrictScalars (algebraMap R' A')).map (α.f i) ≫
        ModuleCat.ofHom (X := (ModuleCat.restrictScalars (algebraMap R' A')).obj (Z.X i))
            (Y := (ModuleCat.restrictScalars (algebraMap R' B)).obj (Z₁.X i))
          { toFun := fun x => (ζ.f i).hom x
            map_add' := fun x y => (ζ.f i).hom.map_add x y
            map_smul' := fun r x =>
              ((ζ.f i).hom.map_smul (algebraMap R' A' r) (show Z.X i from x)).trans
                (congrArg (fun c : B => c • (show Z₁.X i from (ζ.f i).hom x))
                  (IsScalarTower.algebraMap_apply R' A' B r).symm) } := by
    intro i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    show (α₁.f i).hom (((squareTermComparison R A R' B).app (N.X i)).hom
      ((1 : R') ⊗ₜ[R, algebraMap R R'] m)) = (ζ.f i).hom ((α.f i).hom
        (((squareTermComparison R A R' A').app (N.X i)).hom ((1 : R') ⊗ₜ[R, algebraMap R R'] m)))
    rw [squareTermComparison_tmul, squareTermComparison_tmul, map_one, map_one]
    exact hα i m
  have hfaith : ∀ f g : modelComplex A F N ⟶ ((ModuleCat.restrictScalars
      (modelRingMap R A R' B R₀)).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z₁,
      (modelRestrictIso F N).inv ≫
        ((ModuleCat.restrictScalars (algebraMap R₀ B₀)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f = (modelRestrictIso F N).inv ≫
          ((ModuleCat.restrictScalars (algebraMap R₀ B₀)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map g → f = g := by
    intro f g h
    rw [cancel_epi] at h
    ext i x
    exact congrArg (fun φ => (φ.f i).hom x) h
  apply hfaith
  have e1 := modelMapX_restrict (R := R) (A := A) (R' := R') (A' := B) (R₀ := R₀) ε N
  have e2 := modelMapX_restrict (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) ε N
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, reassoc_of% e1, Category.assoc,
    reassoc_of% e2]
  congr 1
  ext i x
  exact congrArg (fun φ => φ.hom x) (key i)

include hF in
/-- If the model map of the square with `A'` replaced by its localization `B` at `q` is a
localization at the elements becoming units in `B`, the model map of the square localizes to a
bijection at the preimage of `q`. -/
theorem bijective_localizedModule_map_of_isLocalizedModule
    (hsurj : Function.Surjective (algebraMap R₀ R'))
    (hpush : Function.Bijective (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')))
    [IsLocalization.AtPrime B q]
    (N : CochainComplex (ModuleCat.{u} A) ℤ) (Z : CochainComplex (ModuleCat.{u} A') ℤ)
    (α : ((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N ⟶ Z)
    (Z₁ : CochainComplex (ModuleCat.{u} B) ℤ)
    (ζ : Z ⟶ ((ModuleCat.restrictScalars (algebraMap A' B)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj Z₁)
    (hζ : ∀ i, IsLocalizedModule q.primeCompl (ζ.f i).hom)
    (α₁ : ((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N ⟶ Z₁)
    (hα : ∀ i (m : N.X i), (α₁.f i).hom ((1 : B) ⊗ₜ[A,algebraMap A B] m) =
      (ζ.f i).hom ((α.f i).hom ((1 : A') ⊗ₜ[A,algebraMap A A'] m)))
    (hB : IsLocalizedModule (IsLocalizedModule.unitsComap (modelRingMap R A R' B R₀))
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n).map
        (DerivedCategory.Q.map (modelKappa (R := R) (A := A) (R' := R') (A' := B) (R₀ := R₀)
          ε N Z₁ α₁))).hom) :
    Function.Bijective (LocalizedModule.map (q.comap (modelRingMap R A R' A' R₀)).primeCompl
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n).map
        (DerivedCategory.Q.map (modelKappa (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀)
          ε N Z α))).hom) := by
  have hρ : Function.Surjective (modelRingMap R A R' A' R₀) :=
    hpush.2.comp (TensorProduct.map_surjective Function.surjective_id hsurj)
  have hU : IsLocalizedModule.unitsComap (modelRingMap R A R' B R₀) =
      (q.comap (modelRingMap R A R' A' R₀)).primeCompl := by
    ext x
    show IsUnit (modelRingMap R A R' B R₀ x) ↔ _
    rw [modelRingMap_apply_of_algebra (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) B x,
      IsLocalization.AtPrime.isUnit_to_map_iff B q]
    rfl
  rw [hU, modelKappa_algebra_eq (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) ε B N Z α Z₁ ζ
    α₁ hα, DerivedCategory.Q.map_comp, Functor.map_comp, ModuleCat.hom_comp] at hB
  have hζ' : ∀ i, IsLocalizedModule (q.comap (modelRingMap R A R' A' R₀)).primeCompl
      ((modelTargetMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) B Z Z₁ ζ).f i).hom := by
    intro i
    have h1 := (ModuleCat.isLocalizedModule_restrictScalars_iff (modelRingMap R A R' A' R₀) hρ
      q.primeCompl (ζ.f i)).2 (hζ i)
    let e : (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).obj
        ((ModuleCat.restrictScalars (algebraMap A' B)).obj (Z₁.X i)) ≃ₗ[B₀]
        (ModuleCat.restrictScalars (modelRingMap R A R' B R₀)).obj (Z₁.X i) :=
      { toFun := fun x => x
        invFun := fun x => x
        map_add' := fun _ _ => rfl
        map_smul' := fun b x => congrArg (fun c : B => c • (show Z₁.X i from x))
          (modelRingMap_apply_of_algebra (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀)
            B b).symm
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have h1' : IsLocalizedModule (q.comap (modelRingMap R A R' A' R₀)).primeCompl
        ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).map (ζ.f i)).hom := h1
    exact IsLocalizedModule.of_linearEquiv (q.comap (modelRingMap R A R' A' R₀)).primeCompl
      ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).map (ζ.f i)).hom e
  have hH : IsLocalizedModule (q.comap (modelRingMap R A R' A' R₀)).primeCompl
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n).map (DerivedCategory.Q.map
        (modelTargetMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) B Z Z₁ ζ))).hom :=
    (isLocalizedModule_homologyFunctor_map_Q_iff _ _ n).2
      (CochainComplex.isLocalizedModule_homologyMap _ _ hζ' n)
  exact bijective_localizedModule_map_of_comp _ _ _ hB

end Local

end Global

end RingTheory.TorIndependence

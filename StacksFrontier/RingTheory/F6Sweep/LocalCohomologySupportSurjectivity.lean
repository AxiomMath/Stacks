module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Stabilization
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianObjects
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.Tor.BaseChangeTensorIso
public import StacksFrontier.RingTheory.Dualizing.DerivedLocalization
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory
public import StacksFrontier.RingTheory.LocalCohomology.AffineLocalizationTriangle
public import StacksFrontier.RingTheory.LocalCohomology.BaseChange
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.ExactSequence

/-!
# Changing the support of local cohomology: surjectivity

Let `I ≤ J` be finitely generated ideals of a Noetherian ring `A` and let `M` be an `A`-module.
For every `i` there is a canonical map `Ψ : Hⁱ_{V(J)}(M) ⟶ Hⁱ_{V(I)}(M)`, the degree-`i`
cohomology of the comparison `RΓ_{V(J)} ⟶ RΓ_{V(I)}` of
`Stacks.Algebraization.localCohomologyComparison`. This file proves that `Ψ` is surjective as
soon as the local cohomology of `M_𝔭` with support in the maximal ideal of `A_𝔭` vanishes in
degree `i` for every prime `𝔭 ∈ V(I) \ V(J)`.

The argument is the one of the source: given a class `ξ ∈ Hⁱ_{V(I)}(M)`, Noetherianity provides
a largest intermediate ideal `I ≤ K ≤ J` with `ξ` in the image of `Hⁱ_{V(K)}(M)`; were
`V(K) ≠ V(J)`, a generic point `𝔭` of `V(K)` outside `V(J)` would have
`Hⁱ_{V(K)}(M)_𝔭 = Hⁱ_{𝔭A_𝔭}(M_𝔭) = 0`, and the ideal could be enlarged. Localizing local
cohomology is what most of the file is about: localization is derived extension of scalars along
`A ⟶ A_𝔭`, so Tag 0ALZ applies, but the universes of the localized module and of `A` are
independent, which forces the comparison through `ULift` and through a small model of the
localization.

## Main results

* `Stacks.LocalCohomology.localCohomologyModuleMapOfLE_surjective` — Tag 0DWV, part (1).

## Implementation notes

The small model of the localization and the abstract coreflection it feeds are *not* developed
here: they are `Dualizing.smallLocalization` and its functor, unit and vanishing criteria of
`StacksFrontier/RingTheory/Dualizing/TorsionComplete/SmallLocalization.lean`, and the degreewise and
derived units of `StacksFrontier/RingTheory/Dualizing/LocalCohomology/Coreflection.lean`. The
declarations of the same shape in the namespace `Stacks.LocalCohomology.SupportSurjectivity`
below are one-line specialisations of those, kept only because the modules downstream of this one
refer to them by these names. Two of the names differ in meaning between the two namespaces:
`smallLocalizationUnit` here is the linear map `M →ₗ[A] S⁻¹M`, which is
`Dualizing.smallLocalizationMk`, while `Dualizing.smallLocalizationUnit` is the natural
transformation, which is `smallLocalizationNatTrans` here.

## References

* [Stacks Project, Tag 0DWV](https://stacks.math.columbia.edu/tag/0DWV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Dualizing.Coreflection
open scoped TensorProduct ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

namespace SupportSurjectivity

/-- The canonical comparison for an inclusion `J ≤ K`, applied to a module in degree zero. -/
private abbrev mapOfLE (A : Type u) [CommRing A] (J K : Ideal A) (hJ : J.FG) (hK : K.FG)
    (hJK : J ≤ K) (M : ModuleCat.{v} A) :=
  Stacks.Algebraization.localCohomologyComparison A K J hK hJ hJK
    ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M)


/-- Applying the left adjoint to `homEquiv a` and composing with the counit recovers `a`. -/
private lemma map_homEquiv_comp_counit {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (W : C) (X : D) (a : F.obj W ⟶ X) :
    F.map (adj.homEquiv W X a) ≫ adj.counit.app X = a := by
  exact (adj.homEquiv_counit (g := adj.homEquiv W X a)).symm.trans
    ((adj.homEquiv W X).symm_apply_apply a)

private theorem isIPowerTorsion_ulift
    {A : Type u} [CommRing A] (I : Ideal A)
    (X : Type v) [AddCommGroup X] [Module A X]
    (hX : IsIPowerTorsion A X I) : IsIPowerTorsion A (ULift.{u} X) I := by
  intro x
  obtain ⟨n, hn, hkill⟩ := hX x.down
  refine ⟨n, hn, fun a ha => ?_⟩
  show ULift.up (a • x.down) = 0
  rw [hkill a ha]
  rfl

private theorem derivedPowerTorsion_ulift
    {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)
    (K : DerivedCategory (ModuleCat.{v} A))
    (hK : Dualizing.derivedPowerTorsionProperty A I hI K) :
    Dualizing.derivedPowerTorsionProperty A I hI
      ((ModuleCat.uliftFunctor.{u} A).mapDerivedCategory.obj K) := fun i =>
  isIPowerTorsion_of_iso
    ((Dualizing.mapDerivedCategoryHomologyIso (ModuleCat.uliftFunctor.{u} A) i).app K).symm
    (isIPowerTorsion_ulift I _ (hK i))

private noncomputable def localCohomology_uliftComparison
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (K : DerivedCategory (ModuleCat.{v} A)) :
    (ModuleCat.uliftFunctor.{u} A).mapDerivedCategory.obj
      ((Dualizing.localCohomologyFunctor A I hI ⋙
        (Dualizing.derivedPowerTorsionProperty A I hI).ι).obj K) ⟶
    (Dualizing.localCohomologyFunctor A I hI ⋙
      (Dualizing.derivedPowerTorsionProperty A I hI).ι).obj
        ((ModuleCat.uliftFunctor.{u} A).mapDerivedCategory.obj K) := by
  let U := (ModuleCat.uliftFunctor.{u} A).mapDerivedCategory
  let Psmall := Dualizing.derivedPowerTorsionProperty.{u, v} A I hI
  let Pbig := Dualizing.derivedPowerTorsionProperty.{u, max u v} A I hI
  let Gsmall := Dualizing.localCohomologyFunctor.{u, v} A I hI
  let Gbig := Dualizing.localCohomologyFunctor.{u, max u v} A I hI
  let T := Psmall.ι.obj (Gsmall.obj K)
  have hT : Pbig (U.obj T) :=
    derivedPowerTorsion_ulift I hI T (Psmall.prop_ι_obj (Gsmall.obj K))
  let W : Pbig.FullSubcategory := ⟨U.obj T, hT⟩
  let a : U.obj T ⟶ U.obj K := U.map
    ((Dualizing.localCohomologyAdjunction
      A I hI).counit.app K)
  exact ((Dualizing.localCohomologyAdjunction
    A I hI).homEquiv W (U.obj K) a).hom

private theorem localCohomology_uliftComparison_counit
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (K : DerivedCategory (ModuleCat.{v} A)) :
    localCohomology_uliftComparison A I hI K ≫
      (Dualizing.localCohomologyAdjunction
        A I hI).counit.app ((ModuleCat.uliftFunctor.{u} A).mapDerivedCategory.obj K) =
      (ModuleCat.uliftFunctor.{u} A).mapDerivedCategory.map
        ((Dualizing.localCohomologyAdjunction
          A I hI).counit.app K) := by
  let U := (ModuleCat.uliftFunctor.{u} A).mapDerivedCategory
  let Psmall := Dualizing.derivedPowerTorsionProperty.{u, v} A I hI
  let Pbig := Dualizing.derivedPowerTorsionProperty.{u, max u v} A I hI
  let Gsmall := Dualizing.localCohomologyFunctor.{u, v} A I hI
  let T := Psmall.ι.obj (Gsmall.obj K)
  let W : Pbig.FullSubcategory :=
    ⟨U.obj T, derivedPowerTorsion_ulift I hI T (Psmall.prop_ι_obj (Gsmall.obj K))⟩
  let a : U.obj T ⟶ U.obj K := U.map
    ((Dualizing.localCohomologyAdjunction
      A I hI).counit.app K)
  show ((Dualizing.localCohomologyAdjunction
    A I hI).homEquiv W (U.obj K) a).hom ≫ _ = a
  exact map_homEquiv_comp_counit (Dualizing.localCohomologyAdjunction A I hI) W (U.obj K) a


section SmallLocalization


/-- The localization `S⁻¹M`, shrunk into the universe of `M`. This is
`Dualizing.smallLocalization`, under the name the development downstream of this file uses. -/
noncomputable def smallLocalization {A : Type u} [CommRing A]
    (S : Submonoid A) [Small.{v} S] (M : ModuleCat.{v} A) : ModuleCat.{v} A :=
  Dualizing.smallLocalization S M

/-- The canonical map `M ⟶ S⁻¹M` into the shrunk localization: `Dualizing.smallLocalizationMk`.
Note that the natural transformation it assembles into is `smallLocalizationNatTrans` here and
`Dualizing.smallLocalizationUnit` there. -/
noncomputable def smallLocalizationUnit {A : Type u} [CommRing A]
    (S : Submonoid A) [Small.{v} S] (M : ModuleCat.{v} A) :
    M →ₗ[A] smallLocalization S M :=
  Dualizing.smallLocalizationMk S M

/-- The map into the shrunk localization exhibits it as the localization. -/
lemma smallLocalizationUnit_isLocalizedModule {A : Type u} [CommRing A]
    (S : Submonoid A) [Small.{v} S] (M : ModuleCat.{v} A) :
    IsLocalizedModule S (smallLocalizationUnit S M) :=
  Dualizing.isLocalizedModule_smallLocalizationMk S M

attribute [local instance] smallLocalizationUnit_isLocalizedModule

/-- Localization at `S`, shrunk into the universe of the modules, as an endofunctor of
`ModuleCat.{v} A`: `Dualizing.smallLocalizationFunctor`. -/
noncomputable def smallLocalizationFunctor {A : Type u} [CommRing A]
    (S : Submonoid A) [Small.{v} S] : ModuleCat.{v} A ⥤ ModuleCat.{v} A :=
  Dualizing.smallLocalizationFunctor S

/-- Localization is additive. -/
lemma smallLocalizationFunctor_additive {A : Type u} [CommRing A]
    (S : Submonoid A) [Small.{v} S] : (smallLocalizationFunctor S).Additive :=
  Dualizing.smallLocalizationFunctor_additive S

attribute [local instance] smallLocalizationFunctor_additive

/-- Localization is left exact. -/
lemma smallLocalizationFunctor_preservesFiniteLimits {A : Type u} [CommRing A]
    (S : Submonoid A) [Small.{v} S] : PreservesFiniteLimits (smallLocalizationFunctor S) :=
  Dualizing.smallLocalizationFunctor_preservesFiniteLimits S

attribute [local instance] smallLocalizationFunctor_preservesFiniteLimits

/-- Localization is right exact. -/
lemma smallLocalizationFunctor_preservesFiniteColimits {A : Type u} [CommRing A]
    (S : Submonoid A) [Small.{v} S] : PreservesFiniteColimits (smallLocalizationFunctor S) :=
  Dualizing.smallLocalizationFunctor_preservesFiniteColimits S

attribute [local instance] smallLocalizationFunctor_preservesFiniteColimits

/-- The unit of localization, as a natural transformation of endofunctors of `ModuleCat.{v} A`:
`Dualizing.smallLocalizationUnit`. -/
noncomputable def smallLocalizationNatTrans {A : Type u} [CommRing A]
    (S : Submonoid A) [Small.{v} S] : 𝟭 (ModuleCat.{v} A) ⟶ smallLocalizationFunctor S :=
  Dualizing.smallLocalizationUnit S

/-- If every element of `S` already acts invertibly on `M`, then `M` is its own localization. -/
lemma smallLocalizationUnit_bijective {A : Type u} [CommRing A]
    (S : Submonoid A) [Small.{v} S] (M : ModuleCat.{v} A)
    (h : ∀ s : S, IsUnit (algebraMap A (Module.End A M) s)) :
    Function.Bijective (smallLocalizationUnit S M) :=
  Dualizing.bijective_smallLocalizationMk S M h

/-- The unit is invertible on the image of the localization functor. -/
lemma smallLocalizationNatTrans_obj_isIso {A : Type u} [CommRing A]
    (S : Submonoid A) [Small.{v} S] (M : ModuleCat.{v} A) :
    IsIso ((smallLocalizationNatTrans S).app ((smallLocalizationFunctor S).obj M)) :=
  Dualizing.isIso_smallLocalizationUnit_app_obj S M

/-- The localization functor inverts the unit. -/
lemma smallLocalizationNatTrans_map_isIso {A : Type u} [CommRing A]
    (S : Submonoid A) [Small.{v} S] (M : ModuleCat.{v} A) :
    IsIso ((smallLocalizationFunctor S).map ((smallLocalizationNatTrans S).app M)) :=
  Dualizing.isIso_smallLocalizationFunctor_map_smallLocalizationUnit_app S M


/-- A localization vanishes exactly when every element is killed by an element of the
submonoid. -/
lemma smallLocalization_isZero_iff {A : Type u} [CommRing A]
    (S : Submonoid A) [Small.{v} S] (M : ModuleCat.{v} A) :
    IsZero (smallLocalization S M) ↔ ∀ m : M, ∃ s : S, s • m = 0 :=
  Dualizing.isZero_smallLocalization_iff S M

/-- The powers of an element form a small submonoid. -/
lemma powers_small {A : Type u} [CommRing A] (f : A) : Small.{v} (Submonoid.powers f) :=
  Dualizing.small_submonoidPowers f

attribute [local instance] powers_small

/-- A derived localization vanishes exactly when it vanishes on every cohomology module. -/
lemma derivedLocalization_isZero_iff {A : Type u} [CommRing A]
    (S : Submonoid A) [Small.{v} S] (X : DerivedCategory (ModuleCat.{v} A)) :
    IsZero ((smallLocalizationFunctor S).mapDerivedCategory.obj X) ↔
      ∀ i, IsZero (smallLocalization S ((DerivedCategory.homologyFunctor _ i).obj X)) :=
  Dualizing.isZero_mapDerivedCategory_smallLocalization_iff S X

/-- Derived localization at `S` kills the derived localization at `T` of anything it kills. -/
lemma derivedLocalization_preserves_kernel {A : Type u} [CommRing A]
    (S T : Submonoid A) [Small.{v} S] [Small.{v} T]
    (X : DerivedCategory (ModuleCat.{v} A))
    (h : IsZero ((smallLocalizationFunctor S).mapDerivedCategory.obj X)) :
    IsZero ((smallLocalizationFunctor S).mapDerivedCategory.obj
      ((smallLocalizationFunctor T).mapDerivedCategory.obj X)) :=
  Dualizing.isZero_mapDerivedCategory_smallLocalization_comp S T X h

/-- An object of `D(A)` has `I`-power-torsion cohomology exactly when it dies under derived
localization at the powers of each generator of `I`. -/
lemma derivedPowerTorsion_iff_localizations
    {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)
    (s : Finset A) (hs : Ideal.span (s : Set A) = I)
    (X : DerivedCategory (ModuleCat.{v} A)) :
    Dualizing.derivedPowerTorsionProperty A I hI X ↔
      ∀ f ∈ s,
        IsZero ((smallLocalizationFunctor (Submonoid.powers f)).mapDerivedCategory.obj X) :=
  Dualizing.derivedPowerTorsionProperty_iff_isZero_mapDerivedCategory I hI s hs X



end SmallLocalization

section CoreflectionTransport


open CategoryTheory.Pretriangulated

private lemma fiber_hom_bijective
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : Triangle C) (hT : T ∈ distTriang C) (W : C)
    (hz : ∀ k : W ⟶ T.obj₃, k = 0)
    (hz' : ∀ k : W ⟶ T.obj₃⟦(-1 : ℤ)⟧, k = 0) :
    Function.Bijective (fun g : W ⟶ T.obj₁ => g ≫ T.mor₁) := by
  have hker : ∀ k : W ⟶ T.obj₁, k ≫ T.mor₁ = 0 → k = 0 := by
    intro k hk
    obtain ⟨k', hk'⟩ := Triangle.coyoneda_exact₂ T.invRotate
      (inv_rot_of_distTriang _ hT) k hk
    rw [hk', hz' k']
    exact zero_comp
  refine ⟨fun k l hkl => ?_, fun k => (Triangle.coyoneda_exact₂ T hT k (hz _)).imp
    fun _ hl => hl.symm⟩
  change k ≫ T.mor₁ = l ≫ T.mor₁ at hkl
  exact sub_eq_zero.mp (hker _ (by rw [Preadditive.sub_comp, hkl, sub_self]))

/-- Postcomposition with an isomorphism is a bijection on morphism sets. -/
private lemma bijective_comp_hom_of_iso {C : Type*} [Category C] {X Y : C} (t : X ≅ Y) (W : C) :
    Function.Bijective (fun g : W ⟶ X => g ≫ t.hom) :=
  ⟨fun _ _ h => (cancel_mono t.hom).1 h, fun g => ⟨g ≫ t.inv, by simp⟩⟩

private lemma exists_localization_coreflection_map
    {C D : Type*} [Category C] [Category D]
    [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (U : C ⥤ D) [U.Additive] [U.CommShift ℤ] [U.IsTriangulated]
    {ι : Type*} (F : ι → C ⥤ C) [∀ i, (F i).Additive]
    [∀ i, (F i).CommShift ℤ] [∀ i, (F i).IsTriangulated]
    (η : ∀ i, 𝟭 C ⟶ F i)
    (hη : ∀ i X, IsIso ((η i).app ((F i).obj X)))
    (hFη : ∀ i X, IsIso ((F i).map ((η i).app X)))
    (hpres : ∀ i j X, IsZero ((F j).obj X) →
      IsZero ((F j).obj ((F i).obj X)))
    (G : ι → D ⥤ D) [∀ i, (G i).CommShift ℤ]
    (θ : ∀ i, 𝟭 D ⟶ G i)
    (hθ : ∀ i X, IsIso ((θ i).app ((G i).obj X)))
    (e : ∀ i X, U.obj ((F i).obj X) ≅ (G i).obj (U.obj X))
    (s : Finset ι) (X : C) :
    ∃ (Y : C) (a : Y ⟶ X), (∀ i ∈ s, IsZero ((F i).obj Y)) ∧
      (∀ W, (∀ i ∈ s, IsZero ((F i).obj W)) →
        Function.Bijective (fun g : W ⟶ Y => g ≫ a)) ∧
      (∀ W, (∀ i ∈ s, IsZero ((G i).obj W)) →
        Function.Bijective (fun g : W ⟶ U.obj Y => g ≫ U.map a)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨X, 𝟙 X, by simp, fun W _ => bijective_comp_hom_of_iso (Iso.refl X) W,
      fun W _ => bijective_comp_hom_of_iso (U.mapIso (Iso.refl X)) W⟩
  | @insert i s hi ih =>
    obtain ⟨Y, b, hY, hb, hbU⟩ := ih
    obtain ⟨T, hT, h₂, h₃, hFT, ha⟩ :=
      Dualizing.Coreflection.exists_fiber_localization (F i) (η i) (hη i) (hFη i) Y
    let t : T.obj₂ ≅ Y := eqToIso h₂
    refine ⟨T.obj₁, T.mor₁ ≫ t.hom ≫ b, ?_, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hFT
      · apply Triangle.isZero₁_of_isZero₂₃ _ ((F j).map_distinguished _ hT)
        · exact (hY j hj).of_iso ((F j).mapIso t)
        · rw [show ((F j).mapTriangle.obj T).obj₃ = (F j).obj T.obj₃ from rfl, h₃]
          exact hpres i j Y (hY j hj)
    · intro W hW
      have h₁ := ha W (hW i (Finset.mem_insert_self _ _))
      have h₂' := bijective_comp_hom_of_iso t W
      have h₃' := hb W (fun j hj => hW j (Finset.mem_insert_of_mem hj))
      simpa only [Function.comp_def, Category.assoc] using h₃'.comp (h₂'.comp h₁)
    · intro W hW
      let t₃ : U.obj T.obj₃ ≅ (G i).obj (U.obj Y) :=
        U.mapIso (eqToIso h₃) ≪≫ e i Y
      have hzero {V Z : D} (t : V ≅ (G i).obj Z) (k : W ⟶ V) : k = 0 :=
        (cancel_mono t.hom).1 <|
          (Dualizing.Coreflection.hom_eq_zero_of_localization (G i) (θ i) (hθ i)
            (hW i (Finset.mem_insert_self _ _)) (k ≫ t.hom)).trans zero_comp.symm
      have h₁ := fiber_hom_bijective (U.mapTriangle.obj T)
        (U.map_distinguished T hT) W (hzero t₃)
        (hzero ((shiftFunctor D (-1 : ℤ)).mapIso t₃ ≪≫
          ((G i).commShiftIso (-1)).symm.app (U.obj Y)))
      change Function.Bijective (fun g : W ⟶ U.obj T.obj₁ => g ≫ U.map T.mor₁) at h₁
      have h₂' := bijective_comp_hom_of_iso (U.mapIso t) W
      have h₃' := hbU W (fun j hj => hW j (Finset.mem_insert_of_mem hj))
      simpa only [Function.comp_def, Functor.map_comp, Functor.mapIso_hom, Category.assoc] using
        h₃'.comp (h₂'.comp h₁)

end CoreflectionTransport

section LocalizationTransport


attribute [local instance] smallLocalizationUnit_isLocalizedModule
  smallLocalizationFunctor_additive smallLocalizationFunctor_preservesFiniteLimits
  smallLocalizationFunctor_preservesFiniteColimits powers_small

/-- The localization map `M → S⁻¹M` of `smallLocalizationUnit`, transported along `ULift` to a
linear map `ULift M → ULift (S⁻¹M)`. -/
noncomputable def uliftLocalizationUnit
    {A : Type u} [CommRing A] (S : Submonoid A) [Small.{v} S]
    (M : ModuleCat.{v} A) :
    ULift.{u} M →ₗ[A] ULift.{u} (smallLocalization S M) :=
  (ULift.moduleEquiv (R := A)).symm.toLinearMap.comp
    ((smallLocalizationUnit S M).comp (ULift.moduleEquiv (R := A)).toLinearMap)

/-- The lifted map `uliftLocalizationUnit S M` exhibits `ULift (S⁻¹M)` as the localization of
`ULift M` at `S`. -/
lemma uliftLocalizationUnit_isLocalizedModule
    {A : Type u} [CommRing A] (S : Submonoid A) [Small.{v} S]
    (M : ModuleCat.{v} A) : IsLocalizedModule S (uliftLocalizationUnit S M) := by
  let := IsLocalizedModule.of_linearEquiv_right S (smallLocalizationUnit S M)
    (ULift.moduleEquiv (R := A) (M := M))
  exact IsLocalizedModule.of_linearEquiv S _
    (ULift.moduleEquiv (R := A) (M := smallLocalization S M)).symm

attribute [local instance] uliftLocalizationUnit_isLocalizedModule

/-- Localization at `S` commutes with the universe lift `ModuleCat.uliftFunctor`: the two
composites `smallLocalizationFunctor S ⋙ ModuleCat.uliftFunctor A` and
`ModuleCat.uliftFunctor A ⋙ smallLocalizationFunctor S` are naturally isomorphic. -/
noncomputable def smallLocalizationUliftIso
    (A : Type u) [CommRing A] (S : Submonoid A) [Small.{v} S] :
    smallLocalizationFunctor S ⋙ ModuleCat.uliftFunctor.{u, v} A ≅
      ModuleCat.uliftFunctor.{u, v} A ⋙ smallLocalizationFunctor S := by
  let instBig (M : ModuleCat.{max u v} A) := smallLocalizationUnit_isLocalizedModule S M
  let instUlift (M : ModuleCat.{v} A) :
      IsLocalizedModule S
        (show ULift.{u} (M : Type v) →ₗ[A]
            (smallLocalization.{u, max u v} S ((ModuleCat.uliftFunctor.{u, v} A).obj M) :
              Type max u v) from
          smallLocalizationUnit S ((ModuleCat.uliftFunctor.{u, v} A).obj M)) :=
    instBig _
  refine NatIso.ofComponents (fun M =>
    (IsLocalizedModule.linearEquiv S (uliftLocalizationUnit S M)
      (smallLocalizationUnit S ((ModuleCat.uliftFunctor.{u} A).obj M))).toModuleIso) ?_
  intro M N f
  apply ModuleCat.hom_ext
  apply IsLocalizedModule.ext S (uliftLocalizationUnit S M)
    (IsLocalizedModule.map_units
      (smallLocalizationUnit S ((ModuleCat.uliftFunctor.{u} A).obj N)))
  ext x
  change (IsLocalizedModule.linearEquiv S (uliftLocalizationUnit S N)
      (smallLocalizationUnit S ((ModuleCat.uliftFunctor.{u} A).obj N)))
        (ULift.up ((IsLocalizedModule.map S (smallLocalizationUnit S M)
          (smallLocalizationUnit S N) f.hom) ((smallLocalizationUnit S M) x.down))) =
    (IsLocalizedModule.map S
      (smallLocalizationUnit S ((ModuleCat.uliftFunctor.{u} A).obj M))
      (smallLocalizationUnit S ((ModuleCat.uliftFunctor.{u} A).obj N))
      ((ModuleCat.uliftFunctor.{u} A).map f).hom)
        ((IsLocalizedModule.linearEquiv S (uliftLocalizationUnit S M)
          (smallLocalizationUnit S ((ModuleCat.uliftFunctor.{u} A).obj M)))
            (uliftLocalizationUnit S M x))
  have hmap : ((IsLocalizedModule.map S (smallLocalizationUnit S M)
        (smallLocalizationUnit S N)) f.hom) ((smallLocalizationUnit S M) x.down) =
      (smallLocalizationUnit S N) (f.hom x.down) :=
    IsLocalizedModule.map_apply S _ _ f.hom x.down
  rw [hmap, IsLocalizedModule.linearEquiv_apply S (uliftLocalizationUnit S M)
    (smallLocalizationUnit S ((ModuleCat.uliftFunctor.{u} A).obj M))]
  exact (IsLocalizedModule.linearEquiv_apply S (uliftLocalizationUnit S N)
    (smallLocalizationUnit S ((ModuleCat.uliftFunctor.{u} A).obj N))
    (ULift.up (f.hom x.down))).trans
      (IsLocalizedModule.map_apply S
        (smallLocalizationUnit S ((ModuleCat.uliftFunctor.{u} A).obj M))
        (smallLocalizationUnit S ((ModuleCat.uliftFunctor.{u} A).obj N))
        ((ModuleCat.uliftFunctor.{u} A).map f).hom x).symm

private noncomputable def mapDerivedCategoryCompIso
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : DerivedCategory C) :
    (F ⋙ G).mapDerivedCategory.obj K ≅
      G.mapDerivedCategory.obj (F.mapDerivedCategory.obj K) := by
  let P := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  exact (F ⋙ G).mapDerivedCategory.mapIso e.symm ≪≫
    (F ⋙ G).mapDerivedCategoryFactors.app P ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
        (.up ℤ)).symm.app P) ≪≫
    (G.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (.up ℤ)).obj P)).symm ≪≫
    G.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app P).symm ≪≫
    G.mapDerivedCategory.mapIso (F.mapDerivedCategory.mapIso e)

private noncomputable def derivedLocalizationUliftIso
    (A : Type u) [CommRing A] (S : Submonoid A) [Small.{v} S]
    (K : DerivedCategory (ModuleCat.{v} A)) :
    (ModuleCat.uliftFunctor.{u} A).mapDerivedCategory.obj
      ((smallLocalizationFunctor S).mapDerivedCategory.obj K) ≅
    (smallLocalizationFunctor.{u, max u v} S).mapDerivedCategory.obj
      ((ModuleCat.uliftFunctor.{u, v} A).mapDerivedCategory.obj K) :=
  by
    let F : ModuleCat.{v} A ⥤ ModuleCat.{v} A := smallLocalizationFunctor S
    let U : ModuleCat.{v} A ⥤ ModuleCat.{max u v} A := ModuleCat.uliftFunctor.{u} A
    let G : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} A := smallLocalizationFunctor S
    let e : F ⋙ U ≅ U ⋙ G := smallLocalizationUliftIso.{u, v} A S
    exact (mapDerivedCategoryCompIso F U K).symm ≪≫
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso (F ⋙ U) (U ⋙ G)
        e).app K ≪≫
      mapDerivedCategoryCompIso U G K

end LocalizationTransport

section CoreflectionComparison


private lemma isIso_of_coreflection_comparison
    {C : Type*} [Category C] {X Y Z : C}
    (a : Y ⟶ X) (b : Z ⟶ X) (f : Y ⟶ Z) (hf : f ≫ b = a)
    (haY : Function.Injective (fun g : Y ⟶ Y => g ≫ a))
    (haZ : Function.Surjective (fun g : Z ⟶ Y => g ≫ a))
    (hbZ : Function.Injective (fun g : Z ⟶ Z => g ≫ b)) : IsIso f := by
  obtain ⟨g, hg⟩ := haZ b
  change g ≫ a = b at hg
  refine ⟨⟨g, haY ?_, hbZ ?_⟩⟩
  · show (f ≫ g) ≫ a = (𝟙 Y) ≫ a
    rw [Category.assoc, hg, hf, Category.id_comp]
  · show (g ≫ f) ≫ b = (𝟙 Z) ≫ b
    rw [Category.assoc, hf, hg, Category.id_comp]

private lemma localCohomology_counit_bijective
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (K W : DerivedCategory (ModuleCat.{v} A))
    (hW : Dualizing.derivedPowerTorsionProperty A I hI W) :
    Function.Bijective (fun g : W ⟶
      (Dualizing.localCohomologyFunctor A I hI ⋙
        (Dualizing.derivedPowerTorsionProperty A I hI).ι).obj K =>
      g ≫ (Dualizing.localCohomologyAdjunction
        A I hI).counit.app K) := by
  let P := Dualizing.derivedPowerTorsionProperty A I hI
  let V : P.FullSubcategory := ⟨W, hW⟩
  let adj := Dualizing.localCohomologyAdjunction A I hI
  let e := P.fullyFaithfulι.homEquiv.symm.trans (adj.homEquiv V K).symm
  have he : (fun g => g ≫ adj.counit.app K) = e := by
    funext g
    exact (adj.homEquiv_counit (g := P.fullyFaithfulι.homEquiv.symm g)).symm
  show Function.Bijective (fun g : P.ι.obj V ⟶
    P.ι.obj ((Dualizing.localCohomologyRightAdjoint
      A I hI).1.obj K) => g ≫ adj.counit.app K)
  exact he.symm ▸ e.bijective

attribute [local instance] smallLocalizationUnit_isLocalizedModule
  smallLocalizationFunctor_additive smallLocalizationFunctor_preservesFiniteLimits
  smallLocalizationFunctor_preservesFiniteColimits powers_small

private theorem localCohomology_uliftComparison_isIso
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (K : DerivedCategory (ModuleCat.{v} A)) :
    IsIso (localCohomology_uliftComparison A I hI K) := by
  classical
  let s := Classical.choose hI
  have hs := Classical.choose_spec hI
  let U := (ModuleCat.uliftFunctor.{u} A).mapDerivedCategory
  let F : A → DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{v} A) :=
    fun f => (smallLocalizationFunctor (Submonoid.powers f)).mapDerivedCategory
  let η : ∀ f, 𝟭 (DerivedCategory (ModuleCat.{v} A)) ⟶ F f := fun f =>
    derivedUnit (smallLocalizationFunctor (Submonoid.powers f))
      (smallLocalizationNatTrans (Submonoid.powers f))
  let G : A → DerivedCategory (ModuleCat.{max u v} A) ⥤
      DerivedCategory (ModuleCat.{max u v} A) :=
    fun f => (smallLocalizationFunctor (Submonoid.powers f)).mapDerivedCategory
  let θ : ∀ f, 𝟭 (DerivedCategory (ModuleCat.{max u v} A)) ⟶ G f := fun f =>
    derivedUnit (smallLocalizationFunctor (Submonoid.powers f))
      (smallLocalizationNatTrans (Submonoid.powers f))
  have hη (f : A) (X : DerivedCategory (ModuleCat.{v} A)) :
      IsIso ((η f).app ((F f).obj X)) :=
    derivedUnit_obj_isIso _ _ (smallLocalizationNatTrans_obj_isIso (Submonoid.powers f)) X
  have hFη (f : A) (X : DerivedCategory (ModuleCat.{v} A)) :
      IsIso ((F f).map ((η f).app X)) :=
    derivedUnit_map_isIso _ _ (smallLocalizationNatTrans_map_isIso (Submonoid.powers f)) X
  have hpres (f g : A) (X : DerivedCategory (ModuleCat.{v} A))
      (h : IsZero ((F g).obj X)) : IsZero ((F g).obj ((F f).obj X)) :=
    derivedLocalization_preserves_kernel (Submonoid.powers g) (Submonoid.powers f) X h
  have hθ (f : A) (X : DerivedCategory (ModuleCat.{max u v} A)) :
      IsIso ((θ f).app ((G f).obj X)) :=
    derivedUnit_obj_isIso _ _ (smallLocalizationNatTrans_obj_isIso (Submonoid.powers f)) X
  obtain ⟨Y, a, hY, ha, haU⟩ := exists_localization_coreflection_map U F η hη hFη hpres
    G θ hθ (fun f X => derivedLocalizationUliftIso A (Submonoid.powers f) X) s K
  let P := Dualizing.derivedPowerTorsionProperty.{u, v} A I hI
  let P' := Dualizing.derivedPowerTorsionProperty.{u, max u v} A I hI
  have hYP : P Y := (derivedPowerTorsion_iff_localizations I hI s hs Y).mpr hY
  have haP (W) (hW : P W) : Function.Bijective (fun g : W ⟶ Y => g ≫ a) :=
    ha W ((derivedPowerTorsion_iff_localizations I hI s hs W).mp hW)
  have haUP (W) (hW : P' W) : Function.Bijective (fun g : W ⟶ U.obj Y => g ≫ U.map a) :=
    haU W ((derivedPowerTorsion_iff_localizations I hI s hs W).mp hW)
  let T := (Dualizing.localCohomologyFunctor A I hI ⋙ P.ι).obj K
  let T' := (Dualizing.localCohomologyFunctor A I hI ⋙ P'.ι).obj (U.obj K)
  have hT : P T := P.prop_ι_obj ((Dualizing.localCohomologyFunctor A I hI).obj K)
  have hT' : P' T' := P'.prop_ι_obj
    ((Dualizing.localCohomologyFunctor A I hI).obj (U.obj K))
  let ε := (Dualizing.localCohomologyAdjunction
    A I hI).counit.app K
  let ε' := (Dualizing.localCohomologyAdjunction
    A I hI).counit.app (U.obj K)
  obtain ⟨c, hc⟩ := (localCohomology_counit_bijective A I hI K Y hYP).surjective a
  have hcIso : IsIso c := isIso_of_coreflection_comparison a ε c hc
    (haP Y hYP).injective (haP T hT).surjective
    (localCohomology_counit_bijective A I hI K T hT).injective
  let k := localCohomology_uliftComparison A I hI K
  have hf : (U.map c ≫ k) ≫ ε' = U.map a := by
    have hassoc : (U.map c ≫ k) ≫ ε' = U.map c ≫ (k ≫ ε') := Category.assoc _ _ _
    rw [hassoc, localCohomology_uliftComparison_counit]
    exact (U.map_comp c ε).symm.trans (congrArg U.map hc)
  have hcomp : IsIso (U.map c ≫ k) :=
    isIso_of_coreflection_comparison (U.map a) ε' _ hf
      (haUP (U.obj Y) (derivedPowerTorsion_ulift I hI Y hYP)).injective
      (haUP T' hT').surjective
      (localCohomology_counit_bijective A I hI (U.obj K) T' hT').injective
  exact (isIso_comp_left_iff (U.map c) k).mp hcomp

end CoreflectionComparison

private noncomputable def localCohomologyModule_uliftIso
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{v} A) (i : ℤ) :
    (ModuleCat.uliftFunctor.{u} A).obj
      (localCohomologyModule A I hI M i) ≅
    localCohomologyModule A I hI
      ((ModuleCat.uliftFunctor.{u} A).obj M) i := by
  let U := ModuleCat.uliftFunctor.{u} A
  let Psmall := Dualizing.derivedPowerTorsionProperty.{u, v} A I hI
  let Pbig := Dualizing.derivedPowerTorsionProperty.{u, max u v} A I hI
  let Gsmall := Dualizing.localCohomologyFunctor.{u, v} A I hI
  let Gbig := Dualizing.localCohomologyFunctor.{u, max u v} A I hI
  let K := (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M
  let L := (Gsmall ⋙ Psmall.ι).obj K
  let eH := (Dualizing.mapDerivedCategoryHomologyIso U i).app L
  let := localCohomology_uliftComparison_isIso A I hI K
  let eC := asIso (localCohomology_uliftComparison A I hI K)
  change U.obj ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj L) ≅ _
  exact eH.symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).mapIso eC ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).mapIso
      ((Gbig ⋙ Pbig.ι).mapIso ((U.mapDerivedCategorySingleFunctor 0).app M))

private noncomputable def localizedModule_uliftEquiv
    {A : Type u} [CommRing A] (S : Submonoid A)
    (X : Type v) [AddCommGroup X] [Module A X] :
    LocalizedModule S (ULift.{u} X) ≃ₗ[Localization S] LocalizedModule S X :=
  LinearEquiv.ofBijective
    (LocalizedModule.map S (ULift.moduleEquiv (R := A) (M := X)).toLinearMap)
    ⟨LocalizedModule.map_injective S _ (ULift.moduleEquiv (R := A) (M := X)).injective,
      LocalizedModule.map_surjective S _ (ULift.moduleEquiv (R := A) (M := X)).surjective⟩


private noncomputable def localCohomologyModule_localizationIso
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{max u v} A) (p : Ideal A) [p.IsPrime] (i : ℤ) :
    (ModuleCat.restrictScalars (algebraMap A (Localization.AtPrime p))).obj
        (localCohomologyModule (Localization.AtPrime p)
          (I.map (algebraMap A (Localization.AtPrime p)))
          (hI.map (algebraMap A (Localization.AtPrime p)))
          (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl M)) i) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i ⋙
        CochainComplex.DerivedTensor.localizedModuleFunctor p.primeCompl).obj
        ((Dualizing.derivedPowerTorsionProperty A I hI).ι.obj
          ((Dualizing.localCohomologyFunctor A I hI).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M))) := by
  let B := Localization.AtPrime p
  let f := algebraMap A B
  let T := p.primeCompl
  let D := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, u} f
  let K := (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M
  let G := ModuleCat.localizedModuleFunctor.{max u v} T
  let eG : G.obj M ≅ ModuleCat.of B (LocalizedModule T M) :=
    LinearEquiv.toModuleIso (Shrink.linearEquiv B (LocalizedModule T M))
  let Kloc : D.functor.obj K ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max u v} B) 0).obj
        (ModuleCat.of B (LocalizedModule T M)) := by
    simpa [K, Functor.comp_obj] using Dualizing.localizationDerivedIso T D K ≪≫
      (Functor.mapDerivedCategorySingleFunctor G 0).app M ≪≫
        (DerivedCategory.singleFunctor (ModuleCat.{max u v} B) 0).mapIso eG
  let L := (Dualizing.derivedPowerTorsionProperty A I hI).ι.obj
    ((Dualizing.localCohomologyFunctor A I hI).obj K)
  let LB := (Dualizing.derivedPowerTorsionProperty B (I.map f) (hI.map f)).ι.obj
    ((Dualizing.localCohomologyFunctor B (I.map f) (hI.map f)).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B) 0).obj
        (ModuleCat.of B (LocalizedModule T M))))
  let eBase := (localCohomologyBaseChangeIso.{u, u, v} f I hI).app K
  let eInput := (Dualizing.derivedPowerTorsionProperty B (I.map f) (hI.map f)).ι.mapIso
    ((Dualizing.localCohomologyFunctor B (I.map f) (hI.map f)).mapIso Kloc)
  let eBC : D.functor.obj L ≅ LB := by
    simpa [L, LB, Functor.comp_obj] using eBase ≪≫ eInput
  let eHom := (DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) i).mapIso eBC
  let eLoc : (ModuleCat.restrictScalars f).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) i).obj (D.functor.obj L)) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i ⋙
        CochainComplex.DerivedTensor.localizedModuleFunctor T).obj L :=
    (CochainComplex.DerivedTensor.derivedExtensionScalarsLocalizationHomologyIso
      T (A := B) i).app L
  simpa [LB, L, f, D, localCohomologyModule,
    CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral,
    Functor.comp_obj] using
    ((ModuleCat.restrictScalars f).mapIso eHom).symm ≪≫ eLoc

private abbrev localCohomologyObject (A : Type u) [CommRing A]
    (I : Ideal A) (hI : I.FG) (M : ModuleCat.{v} A) :=
  (Dualizing.derivedPowerTorsionProperty A I hI).ι.obj
    ((Dualizing.localCohomologyFunctor A I hI).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M))

private abbrev localCohomologyAugmentation (A : Type u) [CommRing A]
    (I : Ideal A) (hI : I.FG) (M : ModuleCat.{v} A) :
    localCohomologyObject A I hI M ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M :=
  (Dualizing.localCohomologyAdjunction A I hI).counit.app _

private abbrev restrictLocalCohomologySupport (A : Type u) [CommRing A]
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG) (hIJ : I ≤ J) (M : ModuleCat.{v} A) :
    Dualizing.PowerTorsionDerivedCategory A I hI :=
  ⟨localCohomologyObject A J hJ M, fun q x ↦ by
    obtain ⟨n, hn, hx⟩ := ((Dualizing.localCohomologyFunctor A J hJ).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M)).property q x
    exact ⟨n, hn, fun a ha ↦ hx a ((pow_le_pow_left' hIJ n) ha)⟩⟩

private abbrev localCohomologyModuleMapOfLE (A : Type u) [CommRing A]
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG) (hIJ : I ≤ J) (M : ModuleCat.{v} A) (i : ℤ) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).map
    (mapOfLE A I J hI hJ hIJ M)

private theorem isColimit_exists_rep_moduleCat
    {A : Type u} [CommRing A] {J : Type u} [Category J] [IsFiltered J] [Nonempty J]
    (F : J ⥤ ModuleCat.{u} A) (D : Cocone F) (hD : IsColimit D)
    (x : D.pt) : ∃ j : J, ∃ y : F.obj j, D.ι.app j y = x := by
  classical
  let ranges : J → Submodule A D.pt := fun j => LinearMap.range (D.ι.app j).hom
  have hdirected : ∀ j k, ∃ l, ranges j ≤ ranges l ∧ ranges k ≤ ranges l := by
    intro j k
    obtain ⟨l, hl⟩ := IsFiltered.sup_objs_exists ({j, k} : Finset J)
    obtain ⟨f⟩ := hl (X := j) (by simp)
    obtain ⟨g⟩ := hl (X := k) (by simp)
    refine ⟨l, ?_, ?_⟩
    · intro z hz
      obtain ⟨m, rfl⟩ := LinearMap.mem_range.mp hz
      refine LinearMap.mem_range.mpr ⟨(F.map f).hom m, ?_⟩
      exact congrArg (fun q => q.hom m) (D.w f)
    · intro z hz
      obtain ⟨m, rfl⟩ := LinearMap.mem_range.mp hz
      refine LinearMap.mem_range.mpr ⟨(F.map g).hom m, ?_⟩
      exact congrArg (fun q => q.hom m) (D.w g)
  let N : Submodule A D.pt := ⨆ j, ranges j
  let legs (j : J) : F.obj j ⟶ ModuleCat.of A N := ModuleCat.ofHom <|
    (D.ι.app j).hom.codRestrict N (fun m =>
      Submodule.mem_iSup_of_mem j (LinearMap.mem_range_self _ m))
  let E : Cocone F := {
    pt := ModuleCat.of A N
    ι := {
      app := legs
      naturality := by
        intro j k f
        apply ModuleCat.hom_ext
        ext m
        apply Subtype.ext
        exact congrArg (fun q => q.hom m) (D.w f)
    }
  }
  let inc : ModuleCat.of A N ⟶ D.pt := ModuleCat.ofHom N.subtype
  have hinc (j : J) : E.ι.app j ≫ inc = D.ι.app j := by
    apply ModuleCat.hom_ext
    ext m
    rfl
  let desc := hD.desc E
  have hdesc : desc ≫ inc = 𝟙 D.pt := by
    apply hD.hom_ext
    intro j
    calc
      D.ι.app j ≫ desc ≫ inc = E.ι.app j ≫ inc := by
        rw [← Category.assoc, hD.fac]
      _ = D.ι.app j := hinc j
      _ = D.ι.app j ≫ 𝟙 D.pt := by simp
  have hxN : x ∈ N := by
    have hx' : inc.hom (desc.hom x) ∈ N := (desc.hom x).property
    have heq : inc.hom (desc.hom x) = x := by
      simpa [ModuleCat.comp_apply] using congrArg (fun f => f.hom x) hdesc
    rwa [heq] at hx'
  obtain ⟨j, hj⟩ := (Submodule.mem_iSup_of_directed ranges hdirected).mp hxN
  exact ⟨j, LinearMap.mem_range.mp hj⟩

private theorem exists_minimalPrime_not_contains_of_radical_ne
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K J : Ideal A) (hKJ : K ≤ J)
    (hrad : K.radical ≠ J.radical) :
    ∃ p : Ideal A, p ∈ K.minimalPrimes ∧ ¬ J ≤ p := by
  by_contra! hall
  have hJrad : J ≤ K.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun p hp => ?_
    have : p.IsPrime := hp.2
    obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le hp.1
    exact (hall q hq).trans hqp
  exact hrad (le_antisymm (Ideal.radical_mono hKJ) (by simpa using Ideal.radical_mono hJrad))

private theorem isIPowerTorsion_iff_of_radical_eq
    {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (I J : Ideal R) (hI : I.FG) (hJ : J.FG)
    (hrad : I.radical = J.radical) :
    IsIPowerTorsion R M I ↔ IsIPowerTorsion R M J := by
  rw [isIPowerTorsion_iff_support_subset R M I hI,
    isIPowerTorsion_iff_support_subset R M J hJ, PrimeSpectrum.zeroLocus_eq_iff.mpr hrad]

private theorem derivedPowerTorsionProperty_iff_of_radical_eq
    {A : Type u} [CommRing A] (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (hrad : I.radical = J.radical) (X : DerivedCategory (ModuleCat.{v} A)) :
    Dualizing.derivedPowerTorsionProperty A I hI X ↔
      Dualizing.derivedPowerTorsionProperty A J hJ X :=
  ⟨fun h n => (isIPowerTorsion_iff_of_radical_eq _ I J hI hJ hrad).mp (h n),
    fun h n => (isIPowerTorsion_iff_of_radical_eq _ I J hI hJ hrad).mpr (h n)⟩

private noncomputable def powerTorsionObjectOfRadicalEq
    {A : Type u} [CommRing A] (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (hrad : I.radical = J.radical)
    (X : Dualizing.PowerTorsionDerivedCategory A I hI) :
    Dualizing.PowerTorsionDerivedCategory A J hJ :=
  ⟨X.1, fun n =>
    (isIPowerTorsion_iff_of_radical_eq _ I J hI hJ hrad).mp (X.2 n)⟩

private theorem localCohomologyMapOfLE_comp_augmentation
    {A : Type u} [CommRing A]
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG) (hIJ : I ≤ J)
    (M : ModuleCat.{v} A) :
    mapOfLE A I J hI hJ hIJ M ≫
        localCohomologyAugmentation A I hI M =
      localCohomologyAugmentation A J hJ M := by
  set X := (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M with hX0
  exact map_homEquiv_comp_counit (Dualizing.localCohomologyAdjunction A I hI)
    (restrictLocalCohomologySupport A I J hI hJ hIJ M) X
    ((Dualizing.localCohomologyAdjunction A J hJ).counit.app X)

private theorem localCohomologyModuleMapOfLE_comp
    {A : Type u} [CommRing A]
    (I K J : Ideal A) (hI : I.FG) (hK : K.FG) (hJ : J.FG)
    (hIK : I ≤ K) (hKJ : K ≤ J) (M : ModuleCat.{v} A) (i : ℤ) :
    localCohomologyModuleMapOfLE A K J hK hJ hKJ M i ≫
      localCohomologyModuleMapOfLE A I K hI hK hIK M i =
    localCohomologyModuleMapOfLE A I J hI hJ (hIK.trans hKJ) M i := by
  classical
  let X := (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M
  let adj := Dualizing.localCohomologyAdjunction A I hI
  let WJ := restrictLocalCohomologySupport A I J hI hJ (hIK.trans hKJ) M
  let WK := restrictLocalCohomologySupport A I K hI hK hIK M
  let LI := (Dualizing.localCohomologyRightAdjoint
    A I hI).1.obj X
  let epsI := localCohomologyAugmentation A I hI M
  let epsJ := localCohomologyAugmentation A J hJ M
  let a : WJ ⟶ WK := ObjectProperty.homMk
    (mapOfLE A K J hK hJ hKJ M)
  let b : WK ⟶ LI := ObjectProperty.homMk
    (mapOfLE A I K hI hK hIK M)
  let c : WJ ⟶ LI := adj.homEquiv WJ X epsJ
  have hleft : (Dualizing.derivedPowerTorsionProperty A I hI).ι.map (a ≫ b) ≫ epsI = epsJ := by
    show (mapOfLE A K J hK hJ hKJ M ≫
      mapOfLE A I K hI hK hIK M) ≫ epsI = epsJ
    rw [Category.assoc, localCohomologyMapOfLE_comp_augmentation I K hI hK hIK M]
    exact localCohomologyMapOfLE_comp_augmentation K J hK hJ hKJ M
  have hright : (Dualizing.derivedPowerTorsionProperty A I hI).ι.map c ≫ epsI = epsJ := by
    show mapOfLE A I J hI hJ (hIK.trans hKJ) M ≫ epsI = epsJ
    exact localCohomologyMapOfLE_comp_augmentation I J hI hJ (hIK.trans hKJ) M
  have hcomp : a ≫ b = c := by
    apply (adj.homEquiv WJ X).symm.injective
    rw [adj.homEquiv_counit, adj.homEquiv_counit]
    exact hleft.trans hright.symm
  show (DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).map
      (mapOfLE A K J hK hJ hKJ M) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).map
        (mapOfLE A I K hI hK hIK M) =
    (DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).map
      (mapOfLE A I J hI hJ (hIK.trans hKJ) M)
  rw [← Functor.map_comp]
  congr 1
  show (Dualizing.derivedPowerTorsionProperty A I hI).ι.map (a ≫ b) =
    (Dualizing.derivedPowerTorsionProperty A I hI).ι.map c
  rw [hcomp]

private theorem isIso_localCohomologyMapOfLE_of_radical_eq
    {A : Type u} [CommRing A]
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG) (hIJ : I ≤ J)
    (hrad : I.radical = J.radical) (M : ModuleCat.{v} A) :
    IsIso (mapOfLE A I J hI hJ hIJ M) := by
  let X := (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M
  have hJJ : Dualizing.derivedPowerTorsionProperty A J hJ (localCohomologyObject A J hJ M) :=
    (Dualizing.derivedPowerTorsionProperty A J hJ).prop_ι_obj
      ((Dualizing.localCohomologyFunctor A J hJ).obj X)
  have hII : Dualizing.derivedPowerTorsionProperty A I hI (localCohomologyObject A I hI M) :=
    (Dualizing.derivedPowerTorsionProperty A I hI).prop_ι_obj
      ((Dualizing.localCohomologyFunctor A I hI).obj X)
  have hIJ' : Dualizing.derivedPowerTorsionProperty A J hJ (localCohomologyObject A I hI M) :=
    (derivedPowerTorsionProperty_iff_of_radical_eq I J hI hJ hrad _).mp hII
  exact isIso_of_coreflection_comparison
    (localCohomologyAugmentation A J hJ M) (localCohomologyAugmentation A I hI M)
    (mapOfLE A I J hI hJ hIJ M)
    (localCohomologyMapOfLE_comp_augmentation I J hI hJ hIJ M)
    (localCohomology_counit_bijective A J hJ X _ hJJ).injective
    (localCohomology_counit_bijective A J hJ X _ hIJ').surjective
    (localCohomology_counit_bijective A I hI X _ hII).injective

private theorem isIso_localCohomologyModuleMapOfLE_of_radical_eq
    {A : Type u} [CommRing A]
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG) (hIJ : I ≤ J)
    (hrad : I.radical = J.radical) (M : ModuleCat.{v} A) (i : ℤ) :
    IsIso (localCohomologyModuleMapOfLE A I J hI hJ hIJ M i) := by
  have : IsIso (mapOfLE A I J hI hJ hIJ M) :=
    isIso_localCohomologyMapOfLE_of_radical_eq I J hI hJ hIJ hrad M
  show IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).map
    (mapOfLE A I J hI hJ hIJ M))
  exact Functor.map_isIso _ _

private theorem exists_maximal_intermediate_support
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I J : Ideal A) (hI : I.FG) (_hJ : J.FG) (hIJ : I ≤ J)
    (M : ModuleCat.{v} A) (i : ℤ)
    (x : localCohomologyModule A I hI M i) :
    ∃ K : Ideal A, ∃ hIK : I ≤ K, ∃ _hKJ : K ≤ J,
      ∃ y : localCohomologyModule A K (Ideal.fg_of_isNoetherianRing K) M i,
        (localCohomologyModuleMapOfLE A I K hI
          (Ideal.fg_of_isNoetherianRing K) hIK M i).hom y = x ∧
        ∀ L : Ideal A, ∀ hIL : I ≤ L, ∀ _hLJ : L ≤ J,
          ∀ yL : localCohomologyModule A L (Ideal.fg_of_isNoetherianRing L) M i,
            (localCohomologyModuleMapOfLE A I L hI
              (Ideal.fg_of_isNoetherianRing L) hIL M i).hom yL = x →
            ¬ K < L := by
  classical
  let f := localCohomologyModuleMapOfLE A I I hI hI le_rfl M i
  have : IsIso f := isIso_localCohomologyModuleMapOfLE_of_radical_eq
    I I hI hI le_rfl rfl M i
  let y₀ := (asIso f).inv.hom x
  let s : Set (Ideal A) := {K | ∃ hIK : I ≤ K, ∃ hKJ : K ≤ J,
    ∃ y : localCohomologyModule A K (Ideal.fg_of_isNoetherianRing K) M i,
      (localCohomologyModuleMapOfLE A I K hI
        (Ideal.fg_of_isNoetherianRing K) hIK M i).hom y = x}
  have hs : s.Nonempty := by
    refine ⟨I, le_rfl, hIJ, y₀, ?_⟩
    dsimp [f, y₀]
    simp
  obtain ⟨K, ⟨hIK, hKJ, y, hy⟩, hmax⟩ :=
    (IsNoetherian.wf (inferInstance : IsNoetherian A A)).has_min s hs
  exact ⟨K, hIK, hKJ, y, hy, fun L hIL hLJ yL hyL => hmax L ⟨hIL, hLJ, yL, hyL⟩⟩


/-- The source of a monomorphism into a subsingleton module is a subsingleton. -/
private lemma subsingleton_of_mono_moduleCat {R : Type u} [Ring R] {X Y : ModuleCat.{v} R}
    (f : X ⟶ Y) [Mono f] (hY : Subsingleton Y) : Subsingleton X :=
  ((ModuleCat.mono_iff_injective f).mp inferInstance).subsingleton

private theorem localized_localCohomology_subsingleton
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{v} A) (p : Ideal A) [p.IsPrime] (i : ℤ)
    (hvan : Subsingleton (localCohomologyModule (Localization.AtPrime p)
      (I.map (algebraMap A (Localization.AtPrime p)))
      (hI.map (algebraMap A (Localization.AtPrime p)))
      (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl M)) i)) :
    Subsingleton (LocalizedModule p.primeCompl (localCohomologyModule A I hI M i)) := by
  let B := Localization.AtPrime p
  let f := algebraMap A B
  let N := (ModuleCat.uliftFunctor.{u} A).obj M
  let eM : ModuleCat.of B (LocalizedModule p.primeCompl N) ≅
      ModuleCat.of B (LocalizedModule p.primeCompl M) :=
    (localizedModule_uliftEquiv p.primeCompl M).toModuleIso
  let eK := (DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) i).mapIso
    (((Dualizing.localCohomologyFunctor B (I.map f) (hI.map f)) ⋙
      (Dualizing.derivedPowerTorsionProperty B (I.map f) (hI.map f)).ι).mapIso
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B) 0).mapIso eM))
  have hN : Subsingleton (localCohomologyModule B (I.map f) (hI.map f)
      (ModuleCat.of B (LocalizedModule p.primeCompl N)) i) :=
    subsingleton_of_mono_moduleCat eK.hom hvan
  let e := localCohomologyModule_localizationIso A I hI N p i
  have hloc : Subsingleton (LocalizedModule p.primeCompl
      (localCohomologyModule A I hI N i)) := by
    exact subsingleton_of_mono_moduleCat e.inv hN
  let eH := localCohomologyModule_uliftIso A I hI M i
  let l := eH.hom.hom.comp (ULift.moduleEquiv (R := A)).symm.toLinearMap
  have hl : Function.Injective l :=
    ((ModuleCat.mono_iff_injective eH.hom).mp inferInstance).comp
      (ULift.moduleEquiv (R := A)).symm.injective
  exact Function.Injective.subsingleton (LocalizedModule.map_injective p.primeCompl l hl)

section EnlargeSupport


open CategoryTheory.Pretriangulated

attribute [local instance] smallLocalizationUnit_isLocalizedModule
  smallLocalizationFunctor_additive smallLocalizationFunctor_preservesFiniteLimits
  smallLocalizationFunctor_preservesFiniteColimits powers_small

private theorem exists_lift_of_smul_eq_zero
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{v} A) (i : ℤ) (f : A)
    (y : localCohomologyModule A I hI M i) (hy : f • y = 0) :
    ∃ z : localCohomologyModule A (I ⊔ Ideal.span {f})
        (Submodule.FG.sup hI (Submodule.fg_span_singleton f)) M i,
      (localCohomologyModuleMapOfLE A I (I ⊔ Ideal.span {f}) hI
        (Submodule.FG.sup hI (Submodule.fg_span_singleton f)) le_sup_left M i).hom z = y := by
  classical
  let S := Submonoid.powers f
  let F := smallLocalizationFunctor S
  let D := F.mapDerivedCategory
  let η := derivedUnit F (smallLocalizationNatTrans S)
  let X := localCohomologyObject A I hI M
  let K := (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle (η.app X)
  let T := (Triangle.mk (η.app X) g h).invRotate
  have hT' : T ∈ distTriang _ := inv_rot_of_distTriang _ hT
  have hF : IsZero (D.obj T.obj₁) :=
    Triangle.isZero₁_of_isIso₂ _ (D.map_distinguished _ hT')
      (derivedUnit_map_isIso F (smallLocalizationNatTrans S)
        (smallLocalizationNatTrans_map_isIso S) X)
  have hIcopy := hI
  obtain ⟨s, hs⟩ := hIcopy
  have hXI : Dualizing.derivedPowerTorsionProperty A I hI X :=
    (Dualizing.localCohomologyFunctor A I hI).obj K |>.property
  have hTI : Dualizing.derivedPowerTorsionProperty A I hI T.obj₁ := by
    apply (derivedPowerTorsion_iff_localizations I hI s hs T.obj₁).mpr
    intro a ha
    let G := (smallLocalizationFunctor (Submonoid.powers a)).mapDerivedCategory
    have hGX : IsZero (G.obj X) :=
      (derivedPowerTorsion_iff_localizations I hI s hs X).mp hXI a ha
    exact Triangle.isZero₁_of_isZero₂₃ _ (G.map_distinguished _ hT') hGX
      (derivedLocalization_preserves_kernel (Submonoid.powers a) S X hGX)
  let L := I ⊔ Ideal.span {f}
  let hL := Submodule.FG.sup hI (Submodule.fg_span_singleton f)
  have hsL : Ideal.span ((insert f s : Finset A) : Set A) = L := by
    simp only [Finset.coe_insert, Ideal.span_insert, hs, L, sup_comm]
  have hTL : Dualizing.derivedPowerTorsionProperty A L hL T.obj₁ :=
    (derivedPowerTorsion_iff_localizations L hL (insert f s) hsL T.obj₁).mpr fun a ha => by
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact hF
      · exact (derivedPowerTorsion_iff_localizations I hI s hs T.obj₁).mp hTI a ha
  let adj := Dualizing.localCohomologyAdjunction A L hL
  let W : Dualizing.PowerTorsionDerivedCategory A L hL := ⟨T.obj₁, hTL⟩
  let a : T.obj₁ ⟶ localCohomologyObject A L hL M :=
    (adj.homEquiv W K (T.mor₁ ≫ localCohomologyAugmentation A I hI M)).hom
  have ha : a ≫ localCohomologyAugmentation A L hL M =
      T.mor₁ ≫ localCohomologyAugmentation A I hI M :=
    map_homEquiv_comp_counit adj W K _
  have hacomp : a ≫ mapOfLE A I L hI hL le_sup_left M =
      T.mor₁ := by
    apply (localCohomology_counit_bijective A I hI K T.obj₁ hTI).injective
    show (a ≫ mapOfLE A I L hI hL le_sup_left M) ≫
      localCohomologyAugmentation A I hI M = _
    calc (a ≫ mapOfLE A I L hI hL le_sup_left M) ≫ localCohomologyAugmentation A I hI M
        = a ≫ (mapOfLE A I L hI hL le_sup_left M ≫
            localCohomologyAugmentation A I hI M) := Category.assoc _ _ _
      _ = a ≫ localCohomologyAugmentation A L hL M :=
          congrArg (fun t => a ≫ t)
            (localCohomologyMapOfLE_comp_augmentation I L hI hL le_sup_left M)
      _ = T.mor₁ ≫ localCohomologyAugmentation A I hI M := ha
  let H := DerivedCategory.homologyFunctor (ModuleCat.{v} A) i
  have hyzero : (H.map T.mor₂).hom y = 0 := by
    let e := (Dualizing.mapDerivedCategoryHomologyIso F i).app X
    have hi := (ModuleCat.mono_iff_injective e.hom).mp inferInstance
    apply hi
    apply IsLocalizedModule.smul_injective (smallLocalizationUnit S (H.obj X))
      (⟨f, Submonoid.mem_powers f⟩ : S)
    show f • e.hom.hom ((H.map T.mor₂).hom y) = f • e.hom.hom 0
    calc
      _ = e.hom.hom ((H.map T.mor₂).hom (f • y)) :=
        (e.hom.hom.map_smul f _).symm.trans
          (congrArg e.hom.hom ((H.map T.mor₂).hom.map_smul f y).symm)
      _ = _ := by
        have h0 : (H.map T.mor₂).hom (f • y) = 0 := by
          rw [hy]; exact map_zero _
        rw [h0, map_zero, smul_zero]
        exact map_zero _
  have hex := DerivedCategory.HomologySequence.exact₂ T hT' i
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hex
  obtain ⟨z, hz⟩ := (hex y).mp hyzero
  refine ⟨(H.map a).hom z, ?_⟩
  have heq : (H.map (a ≫ mapOfLE A I L hI hL le_sup_left M)).hom z = y := by
    rw [hacomp]; exact hz
  rwa [Functor.map_comp, ModuleCat.comp_apply] at heq

end EnlargeSupport

private theorem localCohomologyModuleMapOfLE_surjective_of_local_vanishing
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG) (hIJ : I ≤ J)
    (M : ModuleCat.{v} A) (i : ℤ) (_hi : 0 ≤ i)
    (hvan : ∀ (p : Ideal A) [p.IsPrime], I ≤ p → ¬ J ≤ p →
      IsZero (localCohomologyModule (Localization.AtPrime p)
        (p.map (algebraMap A (Localization.AtPrime p)))
        ((Ideal.fg_of_isNoetherianRing p).map (algebraMap A (Localization.AtPrime p)))
        (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl M)) i)) :
    Function.Surjective
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).map
        (mapOfLE A I J hI hJ hIJ M)).hom := by
  show Function.Surjective
    (localCohomologyModuleMapOfLE A I J hI hJ hIJ M i).hom
  intro x
  classical
  obtain ⟨K, hIK, hKJ, y, hy, hKmax⟩ :=
    exists_maximal_intermediate_support I J hI hJ hIJ M i x
  by_cases hrad : K.radical = J.radical
  · let f := localCohomologyModuleMapOfLE A K J
      (Ideal.fg_of_isNoetherianRing K) hJ hKJ M i
    have : IsIso f := isIso_localCohomologyModuleMapOfLE_of_radical_eq
      K J (Ideal.fg_of_isNoetherianRing K) hJ hKJ hrad M i
    let yJ := (asIso f).inv.hom y
    refine ⟨yJ, ?_⟩
    have hEval := congrArg (fun g => g.hom yJ) (localCohomologyModuleMapOfLE_comp
      I K J hI (Ideal.fg_of_isNoetherianRing K) hJ hIK hKJ M i)
    calc
      (localCohomologyModuleMapOfLE A I J hI hJ hIJ M i).hom yJ =
          (localCohomologyModuleMapOfLE A I K hI
            (Ideal.fg_of_isNoetherianRing K) hIK M i).hom
            ((localCohomologyModuleMapOfLE A K J
              (Ideal.fg_of_isNoetherianRing K) hJ hKJ M i).hom yJ) := by
                simpa [ModuleCat.comp_apply] using hEval.symm
      _ = (localCohomologyModuleMapOfLE A I K hI
            (Ideal.fg_of_isNoetherianRing K) hIK M i).hom y := by
              rw [show f.hom yJ = y by simp [yJ, f]]
      _ = x := hy
  · obtain ⟨p, hpK, hJp⟩ := exists_minimalPrime_not_contains_of_radical_ne K J hKJ hrad
    have hKp : K ≤ p := hpK.1.2
    let : p.IsPrime := hpK.1.1
    let B := Localization.AtPrime p
    let f := algebraMap A B
    let hKfg : K.FG := Ideal.fg_of_isNoetherianRing K
    let hKmap : (K.map f).FG := hKfg.map f
    let hpmap : (p.map f).FG := (Ideal.fg_of_isNoetherianRing p).map f
    have hprimeMap : (p.map f).IsPrime := by
      rw [IsLocalization.AtPrime.map_eq_maximalIdeal]
      exact (IsLocalRing.maximalIdeal.isMaximal B).isPrime
    have hradp : (K.map f).radical = (p.map f).radical := by
      rw [IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
        (A := B) p K hpK, hprimeMap.radical]
    let g := localCohomologyModuleMapOfLE B (K.map f) (p.map f)
      hKmap hpmap (Ideal.map_mono hKp)
      (ModuleCat.of B (LocalizedModule p.primeCompl M)) i
    have : IsIso g := isIso_localCohomologyModuleMapOfLE_of_radical_eq
      (K.map f) (p.map f) hKmap hpmap (Ideal.map_mono hKp) hradp
      (ModuleCat.of B (LocalizedModule p.primeCompl M)) i
    have hpvan : Subsingleton (localCohomologyModule B (p.map f) hpmap
        (ModuleCat.of B (LocalizedModule p.primeCompl M)) i) :=
      ModuleCat.isZero_iff_subsingleton.mp (hvan p (hIK.trans hKp) hJp)
    have hKmapvan : Subsingleton (localCohomologyModule B (K.map f) hKmap
        (ModuleCat.of B (LocalizedModule p.primeCompl M)) i) :=
      subsingleton_of_mono_moduleCat (asIso g).inv hpvan
    have hlocvan := localized_localCohomology_subsingleton A K hKfg M p i hKmapvan
    obtain ⟨s, hs, hsy⟩ :=
      (IsLocalizedModule.subsingleton_iff p.primeCompl
        (LocalizedModule.mkLinearMap p.primeCompl
          (localCohomologyModule A K hKfg M i))).mp hlocvan y
    obtain ⟨a, haJ, hap⟩ := SetLike.not_le_iff_exists.mp hJp
    let b := a * s
    have hbJ : b ∈ J := J.mul_mem_right s haJ
    have hbp : b ∉ p := p.primeCompl.mul_mem hap hs
    have hby : b • y = 0 := by rw [mul_smul, hsy, smul_zero]
    let L := K ⊔ Ideal.span {b}
    let hL := Submodule.FG.sup hKfg (Submodule.fg_span_singleton b)
    have hKL : K ≤ L := le_sup_left
    have hLJ : L ≤ J := sup_le hKJ ((Ideal.span_singleton_le_iff_mem J).mpr hbJ)
    obtain ⟨z, hz⟩ := exists_lift_of_smul_eq_zero A K hKfg M i b y hby
    have hzx : (localCohomologyModuleMapOfLE A I L hI hL (hIK.trans hKL) M i).hom z = x := by
      have heq := congrArg (fun q => q.hom z)
        (localCohomologyModuleMapOfLE_comp I K L hI hKfg hL hIK hKL M i)
      calc
        _ = (localCohomologyModuleMapOfLE A I K hI hKfg hIK M i).hom
            ((localCohomologyModuleMapOfLE A K L hKfg hL hKL M i).hom z) := heq.symm
        _ = x := by rw [hz, hy]
    refine (hKmax L (hIK.trans hKL) hLJ z hzx (lt_of_le_of_ne hKL fun heq => ?_)).elim
    have hbK : b ∈ K := heq ▸ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self b))
    exact hbp (hKp hbK)

end SupportSurjectivity

/-- **Stacks 0DWV, part (1).** Surjectivity of the comparison map.

The covering set of the bare tag `0DWV` is three declarations, one per part of the source. The
other two are `Stacks.LocalCohomology.localCohomologyModuleMapOfLE_injective` and
`Stacks.LocalCohomology.isIso_localCohomologyModuleMapOfLE`. -/
@[stacks 0DWV "surjectivity"]
public theorem localCohomologyModuleMapOfLE_surjective
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG) (hIJ : I ≤ J)
    (M : ModuleCat.{v} A) (i : ℤ) (hi : 0 ≤ i)
    (hvan : ∀ (p : Ideal A) [p.IsPrime], I ≤ p → ¬ J ≤ p →
      IsZero (localCohomologyModule (Localization.AtPrime p)
        (p.map (algebraMap A (Localization.AtPrime p)))
        ((Ideal.fg_of_isNoetherianRing p).map (algebraMap A (Localization.AtPrime p)))
        (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl M)) i)) :
    Function.Surjective
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).map
        (Stacks.Algebraization.localCohomologyComparison A J I hJ hI hIJ
          ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M))).hom :=
  SupportSurjectivity.localCohomologyModuleMapOfLE_surjective_of_local_vanishing
    A I J hI hJ hIJ M i hi hvan

end Stacks.LocalCohomology

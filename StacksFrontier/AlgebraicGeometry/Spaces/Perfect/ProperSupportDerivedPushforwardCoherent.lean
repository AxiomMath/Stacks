module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedModulePushforwardSingle
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperSupportHigherDirectImageCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforwardBound
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerre

/-!
# The derived direct image of a bounded coherent complex with proper support

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type, with `Y` Noetherian, and let `E` be an object of `D^b_Coh(𝒪_X)` whose cohomology sheaves
have support proper over `Y`.  Then `Rf_*E` lies in `D^b_Coh(𝒪_Y)` (Stacks 08GK).

For a module `𝓕` placed in degree `0` the cohomology sheaves of `Rf_*𝓕` are the higher direct
images `R^p f_*𝓕`, coherent by Stacks 08GC.  They vanish in large degrees: `𝓕 = i_*𝓖` for a
closed subspace `i : Z → X` proper over `Y` (Stacks 0CZI), `R^p f_*𝓕 = R^p (f ∘ i)_*𝓖`
(Stacks 0734 with Stacks 07UH), and `f ∘ i` is quasi-compact and quasi-separated over a
quasi-compact base, so Stacks 08FA (2) bounds its direct image.  The objects carried by `Rf_*`
into `D^b_Coh(𝒪_Y)` form a triangulated subcategory, so the general case follows by induction on
the length of the window in which `E` has cohomology.

## Main results

* `AlgebraicGeometry.Space.isCoherent_isWeakSerreClass_smallEtale`: coherent modules on an
  algebraic space form a weak Serre subcategory.
* `AlgebraicGeometry.Space.derivedCategoryBBounded_derivedModulePushforward_single_coherent`: the
  case of a module placed in degree `0`.
* `AlgebraicGeometry.Space.derivedCategoryBBounded_derivedModulePushforward`: the content of
  Stacks 08GK.

## References

* [Stacks Project, Tag 08GK](https://stacks.math.columbia.edu/tag/08GK)
* [Stacks Project, Tag 08GC](https://stacks.math.columbia.edu/tag/08GC)
* [Stacks Project, Tag 08FA](https://stacks.math.columbia.edu/tag/08FA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Coherent modules on an algebraic space form a weak Serre subcategory (Stacks 0754): they
contain `0` and are closed under isomorphisms, kernels, cokernels and extensions (Stacks 07UC). -/
instance isCoherent_isWeakSerreClass_smallEtale (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) : (isCoherent.{u, u} B S hS F hF).IsWeakSerreClass where

attribute [local instance] enoughInjectives_modules_ringUniverse

/-- `Hⁿ(Rf_*(𝓕[0])) ≅ Rⁿf_*𝓕` for a morphism of algebraic spaces and an `𝒪_X`-module `𝓕`. -/
def derivedModulePushforwardSingleHomologyIso {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (n : ℕ) :
    (DerivedCategory.homologyFunctor _ (n : ℤ)).obj ((derivedModulePushforward B S hS f).obj
        ((DerivedCategory.singleFunctor _ 0).obj F)) ≅
      ((modulePushforward B S hS f).rightDerived n).obj F :=
  (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived (modulePushforward B S hS f)
    (derivedModulePushforward B S hS f) (derivedModulePushforwardUnit B S hS f)
    (exists_quasiIso_isKInjective_modules B S hS X.1 X.2) n).app F

/-- **The case of a module.**  Let `f : X ⟶ Y` be locally of finite type with `Y` Noetherian and
let `𝓕` be a coherent `𝒪_X`-module with support proper over `Y`.  Then `Rf_*(𝓕[0])` lies in
`D^b_Coh(𝒪_Y)`. -/
theorem derivedCategoryBBounded_derivedModulePushforward_single_coherent
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hY : IsNoetherian B S hS hZ Y.1)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)
    (hsupp : HasProperSupport B S hS X.2 Y.2 f.hom hf ((SheafOfModules.toSheaf _).obj F)) :
    DerivedCategoryB.derivedCategoryBBounded (isCoherent.{u, u} B S hS Y.1 Y.2)
      ((derivedModulePushforward B S hS f).obj ((DerivedCategory.singleFunctor _ 0).obj F)) := by
  set K := (derivedModulePushforward B S hS f).obj ((DerivedCategory.singleFunctor _ 0).obj F)
  have hGE : K.IsGE 0 := isGE_rightDerived_modulePushforward_obj_singleFunctor B S hS f _
    (derivedModulePushforwardUnit B S hS f) F
  have hneg : ∀ m : ℤ, m < 0 → IsZero ((DerivedCategory.homologyFunctor _ m).obj K) :=
    fun m hm => K.isZero_of_isGE 0 m hm
  obtain ⟨Z, G, hGqc, -, hZp, ⟨e⟩⟩ :=
    ((hasProperSupport_tfae B S hS X Y f.hom hf F hF.toIsQuasicoherentOnSite
      (isFiniteTypeOnSite_of_isCoherentOnSite B S hS X F)
      hF.toIsCoherentOnSite.isFiniteType).out 1 3).1 hsupp
  have hfin : IsFinite B S hS (closedSubspaceInclusion B S hS X Z).hom :=
    isFinite_of_isClosedImmersion B S hS _ Z.2.2
  have hp : IsProper B S hS (closedSubspaceInclusion B S hS X Z ≫ f).hom := hZp
  obtain ⟨N, hN⟩ := exists_isZero_homology_derivedModulePushforward B S hS
    (closedSubspaceInclusion B S hS X Z ≫ f) hp.2.1.2
    (isQuasiSeparated_of_isSeparated B S hS hp.1) hY.1
  have hGq : QcohDerived B S hS (closedSubspaceToSpace B S hS X Z)
      ((DerivedCategory.singleFunctor _ 0).obj G) :=
    (DerivedCategoryB.derivedCategoryBPlus_singleFunctor_obj _
      (WeakSerre.isWeakSerre_of_isWeakSerreClass _) G hGqc).2
  have hpos : ∀ m : ℤ, 0 < m → IsZero ((DerivedCategory.homologyFunctor _ m).obj
      ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS _ _) 0).obj G)) :=
    fun m hm => DerivedCategory.isZero_of_isLE _ 0 m hm
  have hbig : ∀ n : ℕ, N ≤ (n : ℤ) →
      IsZero ((DerivedCategory.homologyFunctor _ (n : ℤ)).obj K) := by
    intro n hn
    have h0 := hN _ hGq hpos n hn
    have e₁ := derivedModulePushforwardSingleHomologyIso B S hS
      (closedSubspaceInclusion B S hS X Z ≫ f) G n
    have e₂ := modulePushforwardRightDerivedCompIso (closedSubspaceInclusion B S hS X Z) f G
      (fun q hq => isZero_rightDerived_modulePushforward_of_isFinite_of_isQuasicoherent B S hS
        (closedSubspaceInclusion B S hS X Z) hfin G hGqc q hq) n
    have e₃ := ((modulePushforward B S hS f).rightDerived n).mapIso e
    exact ((h0.of_iso e₁.symm).of_iso e₂.symm).of_iso
      (derivedModulePushforwardSingleHomologyIso B S hS f F n ≪≫ e₃.symm)
  refine ⟨⟨⟨0, hneg⟩, ⟨max N 0, fun m hm => ?_⟩⟩, fun m => ?_⟩
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ m by omega)
    exact hbig n (by omega)
  · rcases lt_or_ge m 0 with hm | hm
    · exact IsCoherent.of_isZero B S hS Y.1 Y.2 (hneg m hm)
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
      exact (isCoherent.{u, u} B S hS Y.1 Y.2).prop_of_iso
        (derivedModulePushforwardSingleHomologyIso B S hS f F n).symm
        (isCoherent_rightDerived_modulePushforward_of_properSupport B S hS f hf hY.2.2 F hF
          hsupp n)

/-- **The content of Stacks 08GK.**  Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`
which is locally of finite type, with `Y` Noetherian.  Let `E` be an object of `D^b_Coh(𝒪_X)`
such that the support of `Hⁱ(E)` is proper over `Y` for all `i`.  Then `Rf_*E` is an object of
`D^b_Coh(𝒪_Y)`. -/
theorem derivedCategoryBBounded_derivedModulePushforward (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hY : IsNoetherian B S hS hZ Y.1)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : DerivedCategoryB.derivedCategoryBBounded (isCoherent.{u, u} B S hS X.1 X.2) E)
    (hsupp : ∀ i : ℤ, HasProperSupport B S hS X.2 Y.2 f.hom hf
      ((SheafOfModules.toSheaf _).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E))) :
    DerivedCategoryB.derivedCategoryBBounded (isCoherent.{u, u} B S hS Y.1 Y.2)
      ((derivedModulePushforward B S hS f).obj E) := by
  let P := (DerivedCategoryB.derivedCategoryBBounded
    (isCoherent.{u, u} B S hS Y.1 Y.2)).inverseImage (derivedModulePushforward B S hS f)
  have hB := WeakSerre.isWeakSerre_of_isWeakSerreClass (isCoherent.{u, u} B S hS Y.1 Y.2)
  have := DerivedCategoryB.derivedCategoryBBounded_isClosedUnderIsomorphisms _ hB
  have := DerivedCategoryB.derivedCategoryBBounded_isTriangulated _ hB
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hcoh⟩ := hE
  have hGE : E.IsGE a := (DerivedCategory.isGE_iff E a).2 ha
  have hLE : E.IsLE (a + ((b - a).toNat : ℕ)) := by
    refine (DerivedCategory.isLE_iff E _).2 fun i hi => hb i ?_
    have := Int.self_le_toNat (b - a)
    omega
  exact P.prop_of_isGE_of_isLE a _ E hGE hLE fun q _ _ =>
    derivedCategoryBBounded_derivedModulePushforward_single_coherent B S hS hZ f hf hY _
      (hcoh q) (hsupp q)

end AlgebraicGeometry.Space

end

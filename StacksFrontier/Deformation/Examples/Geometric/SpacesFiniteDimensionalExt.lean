module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModelNaiveCotangentHomologyNegOneCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentExtUniverseComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperExtFiniteOverAffineObject
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.Deformation.Examples.Geometric.SpacesFiniteDimensionalResidueFieldAction
public import StacksFrontier.Deformation.Examples.Geometric.SpacesInfinitesimalAutomorphismsLinearDerivations
public import StacksFrontier.Deformation.Examples.Geometric.SpacesInfinitesimalAutomorphismsLinearExtZero
public import StacksFrontier.Deformation.Examples.Geometric.SpacesInfinitesimalAutomorphismsDerivations

/-!
# Finiteness of `Ext` out of `NL_{X/k}` for a proper algebraic space

In the situation of Stacks 0E3Z, let `X` be an algebraic space over the residue field `k`, proper
over `k`.  This file proves that the `k`-vector spaces

`Ext^i_{𝒪_X}(NL_{X/k}, 𝒪_X)`

are finite dimensional for every `i`, which is the content of the proof of Stacks 0E42 once the
identifications of Stacks 0E41 are granted.  The `Ext` groups are those of the naive cotangent
complex `NL_{X/k}` of Stacks 0D0V, whose sections lie in `Type (u + 1)`, with coefficients the unit
module raised to that universe, computed in any model of the derived category; `k` acts through
`Deformation.Examples.spaceResidueFieldRingHom`.

The proof is the source's: `NL_{X/k}` has coherent cohomology sheaves, zero outside degrees `-1`
and `0` (Stacks 0D0Y, 0D0Z for `X` of finite type over `k`:
`AlgebraicGeometry.Space.isCoherent_modelNaiveCotangentHomology_negOne` and
`AlgebraicGeometry.Space.isCoherent_modelNaiveCotangentHomology_zero`), and on the proper `X` the
`Ext` groups from an object of `D⁻_Coh` into one of `D⁺_Coh` are finite (Stacks 0D0T, over the
affine object `Spec k` of the site:
`AlgebraicGeometry.Space.moduleFinite_hom_shift_of_hasFiniteCoherentCohomologyOver`).  The passage
between the universe of the sections of `NL_{X/k}` and the universe of the structure rings, at
which Stacks 0D0T is available, is
`AlgebraicGeometry.Space.moduleFinite_naiveCotangentExt_of_moduleFinite_modelHom`.

## Main results

* `Deformation.Examples.moduleFinite_spaceNaiveCotangentExt`: `Ext^i_{𝒪_X}(NL_{X/k}, 𝒪_X)`.
* `Deformation.Examples.moduleFinite_spaceDifferentialsHom`: `Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X)`.

## References

* [Stacks Project, Tag 0E42](https://stacks.math.columbia.edu/tag/0E42)
* [Stacks Project, Tag 0D0Z](https://stacks.math.columbia.edu/tag/0D0Z)
* [Stacks Project, Tag 0D0T](https://stacks.math.columbia.edu/tag/0D0T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules

universe w u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Finiteness after restricting scalars along a composite `φ ∘ γ` with `γ` surjective follows from
finiteness after restricting scalars along `φ`. -/
theorem moduleFinite_restrictScalars_comp_of_surjective {R₀ R₁ R₂ : Type*} [CommRing R₀]
    [CommRing R₁] [Ring R₂] (γ : R₀ →+* R₁) (hγ : Function.Surjective γ) (φ : R₁ →+* R₂)
    (M : ModuleCat R₂) (h : Module.Finite R₁ ((ModuleCat.restrictScalars φ).obj M)) :
    Module.Finite R₀ ((ModuleCat.restrictScalars (φ.comp γ)).obj M) := by
  have : RingHomSurjective γ := ⟨hγ⟩
  exact (({ toFun := id, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } :
    (ModuleCat.restrictScalars (φ.comp γ)).obj M →ₛₗ[γ]
      (ModuleCat.restrictScalars φ).obj M).finite_iff_of_bijective Function.bijective_id).2 h

/-- A sheaf of modules carried to a zero object by a faithful functor preserving zero morphisms is
a zero object. -/
theorem isZero_of_faithful_of_isZero_obj {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Faithful] [F.PreservesZeroMorphisms] {M : C}
    (h : IsZero (F.obj M)) : IsZero M :=
  (IsZero.iff_id_eq_zero _).2 (F.map_injective
      (by rw [F.map_id, F.map_zero]; exact h.eq_of_src _ _))

/-- The cohomology objects of an object placed in degree `0` vanish outside degree `0`. -/
theorem isZero_homology_singleFunctor_obj {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (M : C) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor C i).obj
        ((DerivedCategory.singleFunctor C 0).obj M)) :=
  (HomologicalComplex.isZero_single_obj_homology (.up ℤ) 0 M i hi).of_iso
    ((DerivedCategory.homologyFunctorFactors C i).app _)

/-- A coherent module placed in degree `0` lies in `D⁻_Coh` and in `D⁺_Coh`. -/
theorem derivedCategoryBMinus_and_plus_singleFunctor_of_isCoherent
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    [HasDerivedCategory.{w} (Space.Modules.{u, u} B S hS X hX)]
    (F : Space.Modules.{u, u} B S hS X hX) (hF : Space.IsCoherent B S hS X hX F) :
    DerivedCategoryB.derivedCategoryBMinus (Space.isCoherent.{u, u} B S hS X hX)
        ((DerivedCategory.singleFunctor (Space.Modules.{u, u} B S hS X hX) 0).obj F) ∧
      DerivedCategoryB.derivedCategoryBPlus (Space.isCoherent.{u, u} B S hS X hX)
        ((DerivedCategory.singleFunctor (Space.Modules.{u, u} B S hS X hX) 0).obj F) := by
  have hB : DerivedCategoryB.derivedCategoryB (Space.isCoherent.{u, u} B S hS X hX)
      ((DerivedCategory.singleFunctor (Space.Modules.{u, u} B S hS X hX) 0).obj F) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      exact Space.isCoherent_of_iso B S hS hX
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F).symm hF
    · exact ObjectProperty.prop_of_isZero (Space.isCoherent.{u, u} B S hS X hX)
        (isZero_homology_singleFunctor_obj F n hn)
  exact ⟨⟨⟨0, fun n hn => isZero_homology_singleFunctor_obj F n (by omega)⟩, hB⟩,
    ⟨⟨0, fun n hn => isZero_homology_singleFunctor_obj F n (by omega)⟩, hB⟩⟩

end AlgebraicGeometry.Space

namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))

/-- The structure morphism `X ⟶ Spec k` of an algebraic space over the residue field, as a
morphism of algebraic spaces. -/
private abbrev spaceStructureHom (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
    (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k))) :
    (⟨X, hX⟩ : AlgebraicSpaces B (Spec (.of Λ)) hΛ) ⟶
      (schemeSpace (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)) :
        AlgebraicSpaces B (Spec (.of Λ)) hΛ) :=
  ObjectProperty.homMk toK

/-- For `X` proper over `Spec k`, the base is locally noetherian, `X` is noetherian and the
cohomology of coherent modules is finite over `k`, acting through `spaceResidueFieldRingHom`. -/
private theorem
    isLocallyNoetherian_and_isNoetherian_and_hasFiniteCoherentCohomologyOver_of_isProper
    (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
    (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))
    (hproper : Space.IsProper B (Spec (.of Λ)) hΛ toK) :
    IsLocallyNoetherian ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).obj
        (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k))) ∧
      Space.IsNoetherian B (Spec (.of Λ)) hΛ B.contains_terminal X ∧
      Space.HasFiniteCoherentCohomologyOver B (Spec (.of Λ)) hΛ X hX
        (spaceResidueFieldRingHom B hΛ hSpec X hX toK) := by
  let V := spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)
  let f := spaceStructureHom B hΛ hSpec X hX toK
  have hVaff : IsAffine ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).obj V) := by
    change IsAffine (Spec _); infer_instance
  have hVN : IsLocallyNoetherian ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).obj V) := by
    change IsLocallyNoetherian (Spec (.of k)); infer_instance
  have hf : Space.IsProper B (Spec (.of Λ)) hΛ f.hom := hproper
  exact ⟨hVN, Space.isNoetherian_of_isProper_toAffine B (Spec (.of Λ)) hΛ V hVaff f hf,
    fun F hF n => Space.moduleFinite_restrictScalars_comp_of_surjective
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2
      (Space.objectRingHom V f) _
      (Space.moduleFinite_cohomology_of_isProper_toAffineObject V hVaff f hf F hF n)⟩

/-- **The `Ext` groups out of `NL_{X/k}` are finite dimensional for `X` proper over `k`.**  In the
situation of Stacks 0E3Z, let `X` be an algebraic space over the residue field `k` which is proper
over `k`.  For every `i` the `k`-vector space `Ext^i_{𝒪_X}(NL_{X/k}, 𝒪_X)` is finite dimensional.

`NL_{X/k}` is the naive cotangent complex of Stacks 0D0V, the coefficients are the unit module at
the universe of its sections, the derived category is any model, and `k` acts through
`Deformation.Examples.spaceResidueFieldRingHom`. -/
private theorem moduleFinite_spaceNaiveCotangentExt_structureSheaf
    (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
    (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))
    (hproper : Space.IsProper B (Spec (.of Λ)) hΛ toK)
    [HasDerivedCategory.{w} (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.structureSheaf B (Spec (.of Λ)) hΛ X hX)))] (i : ℤ) :
    letI : Linear k (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.structureSheaf B (Spec (.of Λ)) hΛ X hX))) :=
      Stacks.SheafOfModules.linearOver _ (spaceResidueFieldRingHom B hΛ hSpec X hX toK)
    Module.Finite k (DerivedCategory.Ext
      (DerivedCategory.Q.obj (Space.naiveCotangentComplex B (Spec (.of Λ)) hΛ
        (spaceStructureHom B hΛ hSpec X hX toK)))
      ((DerivedCategory.singleFunctor _ 0).obj (Stacks.SheafOfModules.uliftUnit.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (Space.structureSheaf B (Spec (.of Λ)) hΛ X hX))))
      i) := by
  refine Space.moduleFinite_naiveCotangentExt_of_moduleFinite_modelHom B (Spec (.of Λ)) hΛ
    (spaceStructureHom B hΛ hSpec X hX toK) (spaceResidueFieldRingHom B hΛ hSpec X hX toK) i ?_
  let V := spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)
  let Xs : AlgebraicSpaces B (Spec (.of Λ)) hΛ := ⟨X, hX⟩
  let f := spaceStructureHom B hΛ hSpec X hX toK
  let φ := spaceResidueFieldRingHom B hΛ hSpec X hX toK
  let := HasDerivedCategory.standard (Space.Modules.{u, u} B (Spec (.of Λ)) hΛ X hX)
  let := HasDerivedCategory.standard (Space.RestrictedModelModules B (Spec (.of Λ)) hΛ Xs)
  let : Linear k (Space.Modules.{u, u} B (Spec (.of Λ)) hΛ X hX) :=
    Stacks.SheafOfModules.linearOver _ φ
  obtain ⟨hVN, hXN, hfin⟩ :=
    isLocallyNoetherian_and_isNoetherian_and_hasFiniteCoherentCohomologyOver_of_isProper B hΛ
      hSpec X hX toK hproper
  have hXln : Space.HasEtaleLocalProperty B (Spec (.of Λ)) hΛ X
      (fun T : Scheme.{u} => IsLocallyNoetherian T) := hXN.2.2
  have hYln : Space.HasEtaleLocalProperty B (Spec (.of Λ)) hΛ (yoneda.obj V)
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    (Space.exists_atlas_iff_of_representable B (Spec (.of Λ)) hΛ (yoneda.obj V)
      (fun T : Scheme.{u} => IsLocallyNoetherian T) V (Iso.refl _)).2 hVN
  have hlft : Space.IsLocallyOfFiniteType B (Spec (.of Λ)) hΛ f.hom := hproper.2.1.1
  -- the objects
  let E := Space.modelModulesEquiv B (Spec (.of Λ)) hΛ Xs
  have : E.functor.Additive :=
    Space.modelModulesEquiv_functor_additive (X := Xs) B (Spec (.of Λ)) hΛ
  have : E.inverse.IsEquivalence := E.isEquivalence_inverse
  let NLm := Space.modelNaiveCotangentComplex B (Spec (.of Λ)) hΛ f
  let K := E.inverse.mapDerivedCategory.obj (DerivedCategory.Q.obj NLm)
  have eH : ∀ n : ℤ, (DerivedCategory.homologyFunctor _ n).obj K ≅
      Space.modelNaiveCotangentHomology B (Spec (.of Λ)) hΛ f n := fun n =>
    (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso E.inverse n).app _ ≪≫
      E.inverse.mapIso ((DerivedCategory.homologyFunctorFactors _ n).app NLm)
  have hzero : ∀ n : ℤ, n ≠ -1 → n ≠ 0 →
      IsZero (Space.modelNaiveCotangentHomology B (Spec (.of Λ)) hΛ f n) := fun n h₁ h₀ =>
    Space.isZero_of_faithful_of_isZero_obj (Space.spaceULift B (Spec (.of Λ)) hΛ Xs)
      ((Space.isZero_homology_naiveCotangentComplex B (Spec (.of Λ)) hΛ f n h₁ h₀).of_iso
        (Space.spaceULiftModelNaiveCotangentHomologyIso B (Spec (.of Λ)) hΛ f n))
  have hcoh : ∀ n : ℤ, Space.IsCoherent B (Spec (.of Λ)) hΛ X hX
      (Space.modelNaiveCotangentHomology B (Spec (.of Λ)) hΛ f n) := by
    intro n
    by_cases h₁ : n = -1
    · subst h₁
      exact Space.isCoherent_modelNaiveCotangentHomology_negOne B (Spec (.of Λ)) hΛ f hlft hXln hYln
    by_cases h₀ : n = 0
    · subst h₀
      exact Space.isCoherent_modelNaiveCotangentHomology_zero B (Spec (.of Λ)) hΛ f hlft hXln
    exact ObjectProperty.prop_of_isZero (Space.isCoherent.{u, u} B (Spec (.of Λ)) hΛ X hX)
        (hzero n h₁ h₀)
  have hK : DerivedCategoryB.derivedCategoryBMinus
      (Space.isCoherent.{u, u} B (Spec (.of Λ)) hΛ X hX) K :=
    ⟨⟨0, fun n hn => (hzero n (by omega) (by omega)).of_iso (eH n)⟩,
      fun n => Space.isCoherent_of_iso B (Spec (.of Λ)) hΛ hX (eH n).symm (hcoh n)⟩
  -- the structure sheaf
  have : Fact (Space.HasEtaleLocalProperty B (Spec (.of Λ)) hΛ X
    (fun T : Scheme.{u} => IsLocallyNoetherian T)) := ⟨hXln⟩
  let O := SheafOfModules.unit
    (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B (Spec (.of Λ)) hΛ X hX).O)
  have hL := (Space.derivedCategoryBMinus_and_plus_singleFunctor_of_isCoherent B (Spec (.of Λ)) hΛ
    X hX O (Space.isCoherent_structureSheaf B (Spec (.of Λ)) hΛ X hX)).2
  exact Space.moduleFinite_hom_shift_of_hasFiniteCoherentCohomologyOver B (Spec (.of Λ)) hΛ X hX
    φ hXN hfin K _ hK hL i

/-- **`Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X)` is finite dimensional for `X` proper over `k`.**  `Ω_{X/k}` is
coherent (Stacks 0D0Z in degree `0`), so the morphisms `Ω_{X/k} ⟶ 𝒪_X`, which are the morphisms
between the two modules placed in degree `0` of the derived category, form a finite `k`-vector
space (Stacks 0D0T).  By Stacks 0E41 this is `Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X) = Der_k(𝒪_X, 𝒪_X)`;
`k` acts through `Deformation.Examples.spaceResidueFieldRingHom`. -/
private theorem moduleFinite_spaceDifferentialsHom_linearOver
    (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
    (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))
    (hproper : Space.IsProper B (Spec (.of Λ)) hΛ toK) :
    letI : Linear k (Space.Modules.{u, u} B (Spec (.of Λ)) hΛ X hX) :=
      Stacks.SheafOfModules.linearOver _ (spaceResidueFieldRingHom B hΛ hSpec X hX toK)
    Module.Finite k (Space.sheafOfDifferentials B (Spec (.of Λ)) hΛ
        (spaceStructureHom B hΛ hSpec X hX toK) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B (Spec (.of Λ)) hΛ X hX).O)) := by
  let V := spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)
  let f := spaceStructureHom B hΛ hSpec X hX toK
  let φ := spaceResidueFieldRingHom B hΛ hSpec X hX toK
  let := HasDerivedCategory.standard (Space.Modules.{u, u} B (Spec (.of Λ)) hΛ X hX)
  let : Linear k (Space.Modules.{u, u} B (Spec (.of Λ)) hΛ X hX) :=
    Stacks.SheafOfModules.linearOver _ φ
  have : HasExt.{u + 1} (Space.Modules.{u, u} B (Spec (.of Λ)) hΛ X hX) :=
    HasExt.standard (Space.Modules.{u, u} B (Spec (.of Λ)) hΛ X hX)
  obtain ⟨-, hXN, hfin⟩ :=
    isLocallyNoetherian_and_isNoetherian_and_hasFiniteCoherentCohomologyOver_of_isProper B hΛ
      hSpec X hX toK hproper
  have hXln : Space.HasEtaleLocalProperty B (Spec (.of Λ)) hΛ X
      (fun T : Scheme.{u} => IsLocallyNoetherian T) := hXN.2.2
  have : Fact (Space.HasEtaleLocalProperty B (Spec (.of Λ)) hΛ X
    (fun T : Scheme.{u} => IsLocallyNoetherian T)) := ⟨hXln⟩
  let Ω := Space.sheafOfDifferentials B (Spec (.of Λ)) hΛ f
  let O := SheafOfModules.unit
    (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B (Spec (.of Λ)) hΛ X hX).O)
  have hK := (Space.derivedCategoryBMinus_and_plus_singleFunctor_of_isCoherent B (Spec (.of Λ)) hΛ
    X hX Ω (Space.isCoherent_sheafOfDifferentials B (Spec (.of Λ)) hΛ f hproper.2.1.1 hXln)).1
  have hL := (Space.derivedCategoryBMinus_and_plus_singleFunctor_of_isCoherent B (Spec (.of Λ)) hΛ
    X hX O (Space.isCoherent_structureSheaf B (Spec (.of Λ)) hΛ X hX)).2
  have h0 := Space.moduleFinite_hom_shift_of_hasFiniteCoherentCohomologyOver B (Spec (.of Λ)) hΛ
    X hX φ hXN hfin _ _ hK hL 0
  exact Module.Finite.equiv
    ((Abelian.Ext.homLinearEquiv (R := k) (X := Ω) (Y := O) (n := 0)).symm.trans
      (Abelian.Ext.linearEquiv₀ (R := k) (X := Ω) (Y := O)))

variable (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
  (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))

/-- **`Ext^i_{𝒪_X}(NL_{X/k}, 𝒪_X)` is finite dimensional for `X` proper over `k`.**  In the
situation of Stacks 0E3Z, let `X` be an algebraic space over the residue field `k` which is proper
over `k`.  For every `i` the `k`-vector space `Ext^i_{𝒪_X}(NL_{X/k}, 𝒪_X)` is finite dimensional.

`NL_{X/k}` is the naive cotangent complex of Stacks 0D0V at the structure morphism
`spaceStructureMap`, the coefficient is `𝒪_X` with its sections raised to the universe of
`NL_{X/k}` (`AlgebraicGeometry.Space.naiveCotangentCoefficient`), the derived category is any
model, and `k` acts through `Deformation.Examples.spaceResidueFieldRingHom`
(`AlgebraicGeometry.Space.naiveCotangentModulesLinear`): the terms of Stacks 0E41.  The proof is
the source's: `NL_{X/k}` has coherent cohomology sheaves, zero outside degrees `-1` and `0`
(Stacks 0D0Z), and on the proper `X` the `Ext` groups from `D⁻_Coh` into `D⁺_Coh` are finite
(Stacks 0D0T). -/
theorem moduleFinite_spaceNaiveCotangentExt (hproper : Space.IsProper B (Spec (.of Λ)) hΛ toK)
    [HasDerivedCategory.{w} (Space.NaiveCotangentModules B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX))]
    (i : ℤ) :
    letI := Space.naiveCotangentModulesLinear B (Spec (.of Λ)) hΛ (X := spaceOf B hΛ X hX)
      (spaceResidueFieldRingHom B hΛ hSpec X hX toK)
    Module.Finite k (DerivedCategory.Ext
      (DerivedCategory.Q.obj (Space.naiveCotangentComplex B (Spec (.of Λ)) hΛ
        (spaceStructureMap B hΛ hSpec X hX toK)))
      ((DerivedCategory.singleFunctor _ 0).obj (Space.naiveCotangentCoefficient B (Spec (.of Λ)) hΛ
        (spaceStructureModule B hΛ (spaceOf B hΛ X hX)))) i) := by
  have h : have : HasDerivedCategory.{w} (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (Space.structureSheaf B (Spec (.of Λ)) hΛ X hX))) :=
        inferInstanceAs (HasDerivedCategory.{w} (Space.NaiveCotangentModules B (Spec (.of Λ)) hΛ
          (spaceOf B hΛ X hX)))
      let : Linear k (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
          (Space.structureSheaf B (Spec (.of Λ)) hΛ X hX))) :=
        Stacks.SheafOfModules.linearOver _ (spaceResidueFieldRingHom B hΛ hSpec X hX toK)
      Module.Finite k (DerivedCategory.Ext
        (DerivedCategory.Q.obj (Space.naiveCotangentComplex B (Spec (.of Λ)) hΛ
          (spaceStructureMap B hΛ hSpec X hX toK)))
        ((DerivedCategory.singleFunctor _ 0).obj (Stacks.SheafOfModules.uliftUnit.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (Space.structureSheaf B (Spec (.of Λ)) hΛ X hX))))
        i) :=
    moduleFinite_spaceNaiveCotangentExt_structureSheaf B hΛ hSpec X hX toK hproper i
  convert h using 3; rfl

/-- **`Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X)` is finite dimensional for `X` proper over `k`**, `k` acting
through `Deformation.Examples.spaceResidueFieldRingHom`
(`AlgebraicGeometry.Space.modulesLinearOfRingHom`): `Ω_{X/k}` is coherent (Stacks 0D0Z in degree
`0`), so the morphisms `Ω_{X/k} ⟶ 𝒪_X`, the morphisms between the two modules placed in degree
`0` of the derived category, form a finite `k`-vector space (Stacks 0D0T). -/
theorem moduleFinite_spaceDifferentialsHom (hproper : Space.IsProper B (Spec (.of Λ)) hΛ toK) :
    letI := (Space.modulesLinearOfRingHom B (Spec (.of Λ)) hΛ (X := spaceOf B hΛ X hX)
      (spaceResidueFieldRingHom B hΛ hSpec X hX toK)).homModule
      (Space.sheafOfDifferentials B (Spec (.of Λ)) hΛ (spaceStructureMap B hΛ hSpec X hX toK))
      (spaceStructureModule B hΛ (spaceOf B hΛ X hX))
    Module.Finite k (Space.sheafOfDifferentials B (Spec (.of Λ)) hΛ
        (spaceStructureMap B hΛ hSpec X hX toK) ⟶
      spaceStructureModule B hΛ (spaceOf B hΛ X hX)) :=
  moduleFinite_spaceDifferentialsHom_linearOver B hΛ hSpec X hX toK hproper

end Deformation.Examples

end

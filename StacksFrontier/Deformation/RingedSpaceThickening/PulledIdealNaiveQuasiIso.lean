module

public import StacksFrontier.Deformation.RingedSpaceThickening.PulledIdealConormal
public import StacksFrontier.Cotangent.SheavesOfRings.ConormalSequenceSurjection
public import StacksFrontier.Cotangent.SheavesOfRings.TowerExtendScalarsShortExact
public import StacksFrontier.Cotangent.SheavesOfRings.BaseChangedNaiveComparison
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentFlatDegreeZero
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# The pulled-back ideal of a thickening is `H^{-1}` of the base-changed naive cotangent complex

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` be a morphism of ringed spaces and `t : (S, 𝒪_S) ⟶ (S', 𝒪_{S'})` a
first order thickening with ideal `𝒥`. On `X` the structure maps form the tower
`(f ∘ t)⁻¹𝒪_{S'} --g--> f⁻¹𝒪_S --h--> 𝒪_X`, with `g` locally surjective. This file proves that the
map from `f^* t^* 𝒥`, placed in degree `-1`, to the base change `NL_{g} ⊗_{f⁻¹𝒪_S} 𝒪_X` of the
naive cotangent complex of `g`, given in degree `-1` by the identification of `f^* t^* 𝒥` with the
base-changed conormal sheaf of `g` followed by the coefficient map into `NL_g`, is a
quasi-isomorphism. This is how the ideal of the deformation problem of Stacks 08UZ is read as the
first vertex of the triangle of the tower.

## Main results

* `CochainComplex.quasiIso_mkHomFromSingle_of_shortExact`: for a cochain complex `N` concentrated
  in degrees `-1` and `0` and a short exact sequence `0 ⟶ K ⟶ N^{-1} ⟶ N^0 ⟶ 0` whose second map
  is the differential, the map from `K` placed in degree `-1` is a quasi-isomorphism. This is the
  converse of `CochainComplex.shortExact_of_quasiIsoAt_of_isZero`.
* `AlgebraicGeometry.RingedSpaceThickening.pulledIdealNaiveMap_f_negOne`: its degree `-1`
  component, `pulledIdealConormalIso` followed by the extension of scalars of the first map of
  `AlgebraicGeometry.RingedSpaceThickening.baseConormalSequence`.
* `AlgebraicGeometry.RingedSpaceThickening.quasiIso_pulledIdealNaiveMap`: the map
  `AlgebraicGeometry.RingedSpaceThickening.pulledIdealNaiveMap` from `f^* t^* 𝒥` in degree `-1`
  to `NL_g ⊗_{f⁻¹𝒪_S} 𝒪_X` is a quasi-isomorphism.

## Implementation notes

The short exact sequence is `0 ⟶ 𝒞 ⟶ NL_g^{-1} ⟶ NL_g^0 ⟶ 0` of
`Stacks.SheafOfModules.shortExact_conormalSheaf_naiveCotangentComplex` for the conormal sheaf `𝒞`
of `g`, which stays short exact after extending scalars along `h` because `NL_g^0` is flat
(`Stacks.SheafOfModules.isFlat_naiveCotangentComplex_X_zero`,
`CategoryTheory.Sheaf.shortExact_map_towerExtendScalars`); its first term `𝒞 ⊗ 𝒪_X` is
`f^* t^* 𝒥` by `AlgebraicGeometry.RingedSpaceThickening.pulledIdealConormalIso`.

## References

* [Stacks Project, Tag 08UZ](https://stacks.math.columbia.edu/tag/08UZ)
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace CochainComplex

variable {𝒞 : Type*} [Category 𝒞] [Abelian 𝒞]

/-- **A two-term complex is quasi-isomorphic to the kernel of its differential, placed in degree
`-1`, when the differential is an epimorphism.** For a cochain complex `N` concentrated in degrees
`-1` and `0` and a short exact sequence `0 ⟶ K ⟶ N^{-1} ⟶ N^0 ⟶ 0` whose second map is the
differential, the map from `K` placed in degree `-1` is a quasi-isomorphism. This is the converse
of `CochainComplex.shortExact_of_quasiIsoAt_of_isZero`. -/
theorem quasiIso_mkHomFromSingle_of_shortExact {N : CochainComplex 𝒞 ℤ}
    (hN : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (N.X i)) {K : 𝒞} (a : K ⟶ N.X (-1))
    (ha : a ≫ N.d (-1) 0 = 0) (hS : (ShortComplex.mk a (N.d (-1) 0) ha).ShortExact) :
    QuasiIso (HomologicalComplex.mkHomFromSingle a (fun k hk => by
      obtain rfl : k = 0 := by simpa using hk.symm
      exact ha)) := by
  set φ := HomologicalComplex.mkHomFromSingle (c := ComplexShape.up ℤ) a (fun k hk => by
      obtain rfl : k = 0 := by simpa using hk.symm
      exact ha)
  have hτ : φ.f (-1) = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1) K).hom ≫ a :=
    HomologicalComplex.mkHomFromSingle_f _ _
  rw [quasiIso_iff]
  intro i
  by_cases h₁ : i = -1
  · subst h₁
    rw [quasiIsoAt_iff' _ (-2) (-1) 0 (by simp) (by simp)]
    refine (ShortComplex.quasiIso_iff_of_zeros _
      (HomologicalComplex.single_obj_d (ComplexShape.up ℤ) _ _ _ _)
      (HomologicalComplex.single_obj_d (ComplexShape.up ℤ) _ _ _ _)
      ((hN (-2) (by decide) (by decide)).eq_of_src _ _)).2 ⟨?_, ?_⟩
    · have hex : (ShortComplex.mk (φ.f (-1)) (N.d (-1) 0)
          (by rw [hτ, Category.assoc, ha, comp_zero])).Exact := by
        refine ShortComplex.exact_of_iso ?_ hS.exact
        refine ShortComplex.isoMk
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1) K).symm
          (Iso.refl _) (Iso.refl _) ?_ ?_
        · dsimp only
          rw [hτ, Iso.symm_hom, Iso.inv_hom_id_assoc, Iso.refl_hom, Category.comp_id]
        · dsimp only
          rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
      exact hex
    · change Mono (φ.f (-1))
      rw [hτ]
      have := hS.mono_f
      exact mono_comp _ _
  by_cases h₀ : i = 0
  · subst h₀
    rw [quasiIsoAt_iff_exactAt _ _ (HomologicalComplex.exactAt_single_obj _ _ _ _ (by decide)),
      HomologicalComplex.exactAt_iff' _ (-1) 0 1 (by simp) (by simp)]
    exact (ShortComplex.exact_iff_epi _ ((hN 1 (by decide) (by decide)).eq_of_tgt _ _)).2
      hS.epi_g
  · rw [quasiIsoAt_iff_exactAt _ _ (HomologicalComplex.exactAt_single_obj _ _ _ _ h₁)]
    exact HomologicalComplex.ExactAt.of_isZero (hN i h₁ h₀)

end CochainComplex

namespace AlgebraicGeometry.RingedSpaceThickening

open RingedSpaceModuleAdjunction
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf)
open Stacks.Sheaves.RingedSpaceCotangent (baseStructureMap structureModules)

variable {X S S' : RingedSpace.{u, u}} (f : X ⟶ S) {t : S ⟶ S'}

local notation "Jₓ" => Opens.grothendieckTopology X.carrier
local notation "hₓ" => Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f

/-- The short exact sequence `0 ⟶ 𝒞 ⟶ NL_{A/A'}.X (-1) ⟶ NL_{A/A'}.X 0 ⟶ 0` of the conormal sheaf
of the locally surjective `g : A' ⟶ A`. -/
abbrev baseConormalSequence (ht : IsFirstOrderThickening t) :=
  haveI := isLocallySurjective_baseStructureMap f ht.1
  ShortComplex.mk _ _ (Stacks.SheafOfModules.trivialConormalMap_comp_naiveCotangentComplex_d
    (inverseImageSheaf (f ≫ t)) (inverseImageSheaf f) (baseStructureMap f t))

variable (t) in
/-- The pulled-back ideal `f^* t^* 𝒥`, as an object of the category
`Stacks.Sheaves.RingedSpaceCotangent.structureModules X` of `𝒪_X`-modules in which the fundamental
triangle of the tower is stated. -/
abbrev pulledIdealModule : structureModules X :=
  (modulePullback f).obj ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t))

variable (t) in
/-- The base change `NL_{A/A'} ⊗_A 𝒪_X` of the naive cotangent complex of the reduction
`A' = (f ∘ t)⁻¹𝒪_{S'} ⟶ A = f⁻¹𝒪_S`, as a complex in
`Stacks.Sheaves.RingedSpaceCotangent.structureModules X`. -/
abbrev pulledNaiveComplex : CochainComplex (structureModules X) ℤ :=
  CategoryTheory.Sheaf.baseChangedNaiveCotangentComplex.{u, u, u} Jₓ (baseStructureMap f t) hₓ

/-- The degree `-1` component of `pulledIdealNaiveMap`: the identification
`f^* t^* 𝒥 ≅ 𝒞 ⊗_A 𝒪_X` of `pulledIdealConormalIso` followed by the extension of scalars of the
coefficient map `𝒞 ⟶ NL_{A/A'}.X (-1)`. -/
def pulledIdealNaiveMapNegOne (ht : IsFirstOrderThickening t) :
    pulledIdealModule f t ⟶ (pulledNaiveComplex f t).X (-1) :=
  CategoryStruct.comp (obj := structureModules X) (X := pulledIdealModule f t)
    (pulledIdealConormalIso f ht).hom
    ((CategoryTheory.Sheaf.towerExtendScalars.{u, u, u} Jₓ hₓ).map (baseConormalSequence f ht).f)

/-- The degree `-1` component of `pulledIdealNaiveMap`, followed by the differential of the
base-changed naive cotangent complex, vanishes. -/
theorem pulledIdealNaiveMapNegOne_comp_d (ht : IsFirstOrderThickening t) :
    pulledIdealNaiveMapNegOne f ht ≫ (pulledNaiveComplex f t).d (-1) 0 = 0 := by
  have := CategoryTheory.Sheaf.towerExtendScalars_additive.{u} Jₓ hₓ
  exact (Category.assoc _ _ _).trans ((congrArg
    (CategoryStruct.comp (obj := structureModules X) (X := pulledIdealModule f t)
      (pulledIdealConormalIso f ht).hom)
    (((CategoryTheory.Sheaf.towerExtendScalars.{u, u, u} Jₓ hₓ).map_comp _ _).symm.trans
      ((congrArg (CategoryTheory.Sheaf.towerExtendScalars.{u, u, u} Jₓ hₓ).map
        (baseConormalSequence f ht).zero).trans
      ((CategoryTheory.Sheaf.towerExtendScalars.{u, u, u} Jₓ hₓ).map_zero _ _)))).trans comp_zero)

/-- **The pulled-back ideal in degree `-1` mapping to the base-changed naive cotangent
complex.** For a morphism of ringed spaces `f : X ⟶ S` and a first order thickening `t : S ⟶ S'`
with ideal `𝒥`, the map of complexes from `f^* t^* 𝒥` placed in degree `-1` to
`NL_{A/A'} ⊗_A 𝒪_X`, where `A' = (f ∘ t)⁻¹𝒪_{S'} ⟶ A = f⁻¹𝒪_S` is the reduction, given in degree
`-1` by the identification `f^* t^* 𝒥 ≅ 𝒞 ⊗_A 𝒪_X` of `pulledIdealConormalIso` followed by the
extension of scalars of the coefficient map `𝒞 ⟶ NL_{A/A'}.X (-1)` of the conormal sheaf `𝒞`. -/
def pulledIdealNaiveMap (ht : IsFirstOrderThickening t) :
    (HomologicalComplex.single (structureModules X) (ComplexShape.up ℤ) (-1)).obj
        (pulledIdealModule f t) ⟶ pulledNaiveComplex f t :=
  HomologicalComplex.mkHomFromSingle (pulledIdealNaiveMapNegOne f ht) (fun k hk => by
    obtain rfl : k = 0 := by simpa using hk.symm
    exact pulledIdealNaiveMapNegOne_comp_d f ht)

/-- The degree `-1` component of `pulledIdealNaiveMap`. -/
theorem pulledIdealNaiveMap_f_negOne (ht : IsFirstOrderThickening t) :
    (pulledIdealNaiveMap f ht).f (-1) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1) _).hom ≫
        pulledIdealNaiveMapNegOne f ht :=
  HomologicalComplex.mkHomFromSingle_f _ _

/-- **`f^* t^* 𝒥` is `H^{-1}` of the base-changed naive cotangent complex.** For a morphism of
ringed spaces `f : X ⟶ S` and a first order thickening `t : S ⟶ S'` with ideal `𝒥`, the map
`pulledIdealNaiveMap` from `f^* t^* 𝒥` placed in degree `-1` to `NL_{A/A'} ⊗_A 𝒪_X` is a
quasi-isomorphism: the sequence `0 ⟶ 𝒞 ⟶ NL_{A/A'}.X (-1) ⟶ NL_{A/A'}.X 0 ⟶ 0` of the conormal
sheaf of `A' ⟶ A` is short exact with flat third term, so it stays short exact after extending
scalars to `𝒪_X`. -/
theorem quasiIso_pulledIdealNaiveMap (ht : IsFirstOrderThickening t) :
    QuasiIso (pulledIdealNaiveMap f ht) := by
  have := isLocallySurjective_baseStructureMap f ht.1
  have hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (baseConormalSequence f ht).X₃ :=
    Stacks.SheafOfModules.isFlat_naiveCotangentComplex_X_zero _ _ _
  have hS₀ : (baseConormalSequence f ht).ShortExact :=
    Stacks.SheafOfModules.shortExact_conormalSheaf_naiveCotangentComplex _ _ _
  have hS := CategoryTheory.Sheaf.shortExact_map_towerExtendScalars.{u} Jₓ hₓ
    (baseConormalSequence f ht) hS₀ hflat
  refine CochainComplex.quasiIso_mkHomFromSingle_of_shortExact
    (CategoryTheory.Sheaf.baseChangedNaiveCotangentComplex_isZero_X.{u, u, u} Jₓ
      (baseStructureMap f t) hₓ)
    (pulledIdealNaiveMapNegOne f ht) (pulledIdealNaiveMapNegOne_comp_d f ht) ?_
  have := CategoryTheory.Sheaf.towerExtendScalars_additive.{u} Jₓ hₓ
  refine ShortComplex.shortExact_of_iso
    (S₁ := (baseConormalSequence f ht).map
      (CategoryTheory.Sheaf.towerExtendScalars.{u, u, u} Jₓ hₓ))
    ?_ hS
  refine ShortComplex.isoMk (pulledIdealConormalIso f ht).symm (Iso.refl _) (Iso.refl _) ?_ ?_
  · exact (Iso.inv_hom_id_assoc _ _).trans (Category.comp_id _).symm
  · exact (Category.id_comp _).trans (Category.comp_id _).symm

end AlgebraicGeometry.RingedSpaceThickening

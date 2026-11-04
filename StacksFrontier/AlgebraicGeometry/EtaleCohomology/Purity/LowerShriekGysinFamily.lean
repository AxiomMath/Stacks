module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.LowerShriekGysin
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.LowerShriekHomologyFiniteDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.HigherDirectImageQuotientRing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage

/-!
# The Gysin map of `R² g_!` on a family of sheaves

Let `i : Z ⟶ U` be finite, `j : U₀ ⟶ U` an open immersion and `g : U ⟶ V` separated of finite
type with a compactification `j_g`, `π = g ∘ i` proper. For a family `T_G` of sheaves of
`Λ`-modules on `U` on which the unit `H ⟶ j_* j⁻¹ H` is an isomorphism, and a family `T_M` of
torsion sheaves on `Z` with `R¹ j_*(j⁻¹ T_G) ≅ i_* T_M` (cohomological purity along the divisor
`Z`), the Gysin map `R⁰ g_!(R¹ j_*(j⁻¹ H)) ⟶ R² g_!(j_* j⁻¹ H)`
(`Stacks.EtaleCohomology.lowerShriekGysin`) becomes a natural map

`π_* T_M ⟶ R² g_! T_G`

(`Stacks.EtaleCohomology.lowerShriekGysinFamily`), through `R⁰ g_!(i_* M) ≅ π_* M`
(`Stacks.EtaleCohomology.lowerShriekHomologyZeroFiniteDirectImageIso`). It is an epimorphism at
`H` as soon as `R^q j_*(j⁻¹ H) = 0` for `q ≥ 2` and `H²(Rg_!(R j_*(j⁻¹ H))) = 0`
(`Stacks.EtaleCohomology.epi_lowerShriekGysinFamily_app`). Applied to the towers of levels of
ℓ-adic sheaves this is the Gysin morphism of the Leray step of the reduction of the weight bound
of Weil II to curves ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

The inputs of cohomological purity are stated for sheaves of `ℤ/N`-modules; the levels of an
ℓ-adic sheaf are read as sheaves of `ℤ_ℓ`-modules. The unit and the higher direct images
commute with restriction of scalars (`Stacks.EtaleCohomology.isIso_unit_restrictScalars`,
`Stacks.EtaleCohomology.isZero_rightDerived_directImage_restrictScalars`).

## Main definitions

* `Stacks.EtaleCohomology.lowerShriekGysinFamily`.

## Main results

* `Stacks.EtaleCohomology.epi_lowerShriekGysinFamily_app`.

## Implementation notes

`Stacks.EtaleCohomology.derivedLowerShriek` lives in the standard model
`HasDerivedCategory.standard`, and so do the statements here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

-- `AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives` has a free universe; with it in scope
-- the instance problems `EnoughInjectives (EtaleModules Λ X)` get stuck on a universe constraint.
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

section RestrictScalars

variable {Λ Λ' : Type} [Ring Λ] [Ring Λ'] (ρ : Λ →+* Λ') {U U₀ : Scheme.{u}} (j : U₀ ⟶ U)
  [IsOpenImmersion j]

/-- **The unit of `j⁻¹ ⊣ j_*` commutes with restriction of scalars**: both functors are
precomposition along functors of small étale sites. -/
theorem etaleModuleRestrictionDirectImageAdj_unit_app_restrictScalars
    (H : EtaleModules.{u, 0} Λ' U) :
    (etaleModuleRestrictionDirectImageAdj.{u, 0} Λ j).unit.app
        ((etaleModuleRestrictScalars ρ U).obj H) =
      (etaleModuleRestrictScalars ρ U).map
        ((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ' j).unit.app H) :=
  rfl

/-- The unit of `j⁻¹ ⊣ j_*` at a sheaf read through restriction of scalars is an isomorphism when
it is one at the sheaf. -/
theorem isIso_unit_restrictScalars (H : EtaleModules.{u, 0} Λ' U)
    (h : IsIso ((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ' j).unit.app H)) :
    IsIso ((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ j).unit.app
      ((etaleModuleRestrictScalars ρ U).obj H)) := by
  rw [etaleModuleRestrictionDirectImageAdj_unit_app_restrictScalars]
  exact Functor.map_isIso _ _

/-- `R^q j_*(j⁻¹ H)` read through restriction of scalars vanishes when it vanishes for `H`. -/
theorem isZero_rightDerived_directImage_restrictScalars (H : EtaleModules.{u, 0} Λ' U) (q : ℕ)
    (h : IsZero (((etaleModuleDirectImage.{u, 0} Λ' j).rightDerived q).obj
      ((etaleModuleRestriction.{u, 0} Λ' j).obj H))) :
    IsZero (((etaleModuleDirectImage.{u, 0} Λ j).rightDerived q).obj
      ((etaleModuleRestriction.{u, 0} Λ j).obj ((etaleModuleRestrictScalars ρ U).obj H))) :=
  IsZero.of_iso (Functor.map_isZero _ h)
    (etaleModuleRightDerivedDirectImageRestrictScalarsIso ρ j
      ((etaleModuleRestriction.{u, 0} Λ' j).obj H) q).symm

end RestrictScalars

section Family

variable (Λ : Type) [Ring Λ] {Z U U₀ V : Scheme.{u}} (i : Z ⟶ U) [IsFinite i] (j : U₀ ⟶ U)
  [IsOpenImmersion j] (g : U ⟶ V) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  [CompactSpace V] [QuasiSeparatedSpace V] (jg : CompactificationOf (Over.mk g)) [IsProper (i ≫ g)]
  {J : Type*} [Category* J] (TG : J ⥤ EtaleModules.{u, 0} Λ U) (TM : J ⥤ EtaleModules.{u, 0} Λ Z)

/-- The torsion sheaves: killed by a positive integer. -/
abbrev torsionEtaleModules (X : Scheme.{u}) : ObjectProperty (EtaleModules.{u, 0} Λ X) :=
  fun Q => ∃ m : ℕ, 0 < m ∧ m • 𝟙 Q = 0

/-- `R⁰ g_!(i_* M) ≅ π_* M` on a family of torsion sheaves. -/
def lowerShriekGysinFamilySourceIso (hTM : ∀ a, torsionEtaleModules Λ Z (TM.obj a)) :
    TM ⋙ etaleModuleDirectImage.{u, 0} Λ (i ≫ g) ≅
      TM ⋙ etaleModuleDirectImage.{u, 0} Λ i ⋙ lowerShriekHomology Λ g jg 0 :=
  (Functor.isoWhiskerLeft (ObjectProperty.lift _ TM hTM)
    (lowerShriekHomologyZeroFiniteDirectImageIso Λ i g jg (torsionEtaleModules Λ Z)
      (fun _ h => h))).symm

/-- `R² g_! H ≅ R² g_!(j_* j⁻¹ H)` on a family on which the unit of `j⁻¹ ⊣ j_*` is an
isomorphism. -/
def lowerShriekGysinFamilyTargetIso
    (hunit : ∀ a, IsIso ((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ j).unit.app (TG.obj a))) :
    TG ⋙ lowerShriekHomology Λ g jg 2 ≅
      TG ⋙ etaleModuleRestriction.{u, 0} Λ j ⋙ etaleModuleDirectImage.{u, 0} Λ j ⋙
        lowerShriekHomology Λ g jg 2 :=
  NatIso.ofComponents
    (fun a => haveI := hunit a
      (lowerShriekHomology Λ g jg 2).mapIso
        (asIso ((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ j).unit.app (TG.obj a))))
    (fun {a b} f => by
      simp only [Functor.comp_map, Functor.mapIso_hom, asIso_hom, ← Functor.map_comp]
      congr 1
      exact (etaleModuleRestrictionDirectImageAdj.{u, 0} Λ j).unit.naturality (TG.map f))

/-- **The Gysin map on a family** `π_* T_M ⟶ R² g_! T_G`: the Gysin map
`R⁰ g_!(R¹ j_*(j⁻¹ H)) ⟶ R² g_!(j_* j⁻¹ H)` read through `R¹ j_*(j⁻¹ T_G) ≅ i_* T_M`,
`R⁰ g_!(i_* M) ≅ π_* M` and the unit `T_G ≅ j_* j⁻¹ T_G`. -/
def lowerShriekGysinFamily
    (e : TG ⋙ etaleModuleRestriction.{u, 0} Λ j ⋙
        (etaleModuleDirectImage.{u, 0} Λ j).rightDerived 1 ≅
      TM ⋙ etaleModuleDirectImage.{u, 0} Λ i)
    (hTM : ∀ a, torsionEtaleModules Λ Z (TM.obj a))
    (hunit : ∀ a, IsIso ((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ j).unit.app (TG.obj a))) :
    TM ⋙ etaleModuleDirectImage.{u, 0} Λ (i ≫ g) ⟶ TG ⋙ lowerShriekHomology Λ g jg 2 :=
  (lowerShriekGysinFamilySourceIso Λ i g jg TM hTM).hom ≫
    Functor.whiskerRight e.inv (lowerShriekHomology Λ g jg 0) ≫
    Functor.whiskerLeft TG (lowerShriekGysin Λ j g jg) ≫
    (lowerShriekGysinFamilyTargetIso Λ j g jg TG hunit).inv

/-- **The Gysin map on a family is an epimorphism** at `a` when `R^q j_*(j⁻¹ T_G(a)) = 0` for
`q ≥ 2` and `H²(Rg_!(R j_*(j⁻¹ T_G(a)))) = 0`. -/
theorem epi_lowerShriekGysinFamily_app
    (e : TG ⋙ etaleModuleRestriction.{u, 0} Λ j ⋙
        (etaleModuleDirectImage.{u, 0} Λ j).rightDerived 1 ≅
      TM ⋙ etaleModuleDirectImage.{u, 0} Λ i)
    (hTM : ∀ a, torsionEtaleModules Λ Z (TM.obj a))
    (hunit : ∀ a, IsIso ((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ j).unit.app (TG.obj a)))
    (a : J)
    (h2 : ∀ q : ℕ, 2 ≤ q → IsZero (((etaleModuleDirectImage.{u, 0} Λ j).rightDerived q).obj
      ((etaleModuleRestriction.{u, 0} Λ j).obj (TG.obj a))))
    (hX : IsZero ((DerivedCategory.Plus.homologyFunctor _ 2).obj
      ((derivedLowerShriek.{u, 0} g jg Λ).obj ((purityComplex Λ j).obj (TG.obj a))))) :
    Epi ((lowerShriekGysinFamily Λ i j g jg TG TM e hTM hunit).app a) := by
  have := epi_lowerShriekGysin_app Λ j g jg (TG.obj a) h2 hX
  simp only [lowerShriekGysinFamily, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  infer_instance

end Family

end Stacks.EtaleCohomology

end

module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DerivedStalkModel
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.RingTheory.Dualizing.UbiquityDualizingComplexes.FlatBaseChange

/-!
# The dimension function of a complex is local

Let `j : Y ⟶ X` be an open immersion of locally Noetherian schemes and `K ∈ D(𝒪_X)`. The stalk of
`K|_Y` at `y` is the stalk of `K` at `j y`, read over `𝒪_{Y,y} ≅ 𝒪_{X,j y}`, so a shift of one is
a normalized dualizing complex exactly when the same shift of the other is. Hence the function
`δ` of [Stacks, Tag 0AWF] of `K|_Y` is the restriction of that of `K`.

## Main results

* `Dualizing.isNormalizedDualizingComplex_restrictScalars_of_bijective` — a normalized dualizing
  complex stays normalized under restriction of scalars along a ring isomorphism.
* `Stacks.Duality.isNormalizedDualizingComplex_derivedStalkOfComplex_restrict_iff` — the stalk of
  the restriction of a complex is normalized exactly when the stalk of the complex is.
* `Stacks.Duality.associatedShiftFunction_restrict_of_isOpenImmersion` — `δ_{K|_Y}(y) = δ_K(j y)`.
* `Stacks.Duality.associatedShiftFunction_congr` — `δ` depends only on the isomorphism class.

## References

* [Stacks Project, Tag 0AWF](https://stacks.math.columbia.edu/tag/0AWF)
* [Stacks Project, Tag 0AWD](https://stacks.math.columbia.edu/tag/0AWD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w w'

attribute [local instance] HasDerivedCategory.standard

namespace Dualizing

/-- **Restriction of scalars along a ring isomorphism preserves normalized dualizing complexes.**
For a bijective ring map `φ : A → B` of Noetherian local rings, restriction of scalars along `φ`
is extension of scalars along `φ⁻¹`, a flat local map carrying the maximal ideal onto the maximal
ideal, so [Stacks, Tag 0AWD] applies. -/
theorem isNormalizedDualizingComplex_restrictScalars_of_bijective {A B : Type u} [CommRing A]
    [CommRing B] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (hφ : Function.Bijective φ) (M : DerivedCategory (ModuleCat.{u} B))
    (hM : IsNormalizedDualizingComplex.{u, u} M) :
    IsNormalizedDualizingComplex.{u, u}
      ((ModuleCat.restrictScalars.{u} φ).mapDerivedCategory.obj M) := by
  let e : A ≃+* B := RingEquiv.ofBijective φ hφ
  let : Algebra B A := e.symm.toRingHom.toAlgebra
  have hflat : (algebraMap B A).Flat := RingHom.Flat.of_bijective e.symm.bijective
  have : Module.Flat B A := hflat
  have : IsLocalHom (algebraMap B A) := IsLocalHom.of_surjective _ e.symm.surjective
  have hmax : (IsLocalRing.maximalIdeal B).map (algebraMap B A) = IsLocalRing.maximalIdeal A :=
    IsLocalRing.map_ringEquiv_maximalIdeal e.symm
  have h := isNormalizedDualizingComplex_extendScalars_of_flat.{u, u, u} hmax M hM
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap B A)) :=
    extendScalars_preservesFiniteLimits_of_flat' _ hflat
  have eF : ModuleCat.extendScalars.{u, u, u} (algebraMap B A) ≅
      ModuleCat.restrictScalars.{u} φ :=
    Stacks.Duality.extendScalarsSymmIsoRestrictScalars e ≪≫
      ModuleCat.restrictScalarsCongr (by ext; rfl)
  exact (isNormalizedDualizingComplex_congr.{u, u}
    ((Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _ eF).app M)).mp h

end Dualizing

namespace Stacks.Duality

open Stacks.DerivedCategoryComparisons

/-- The function `δ` of [Stacks, Tag 0AWF] depends only on the isomorphism class of the complex. -/
theorem associatedShiftFunction_congr {X : Scheme.{u}} [IsLocallyNoetherian X]
    [HasDerivedCategory.{w} X.Modules] {K K' : DerivedCategory X.Modules} (e : K ≅ K') :
    associatedShiftFunction K = associatedShiftFunction K' := by
  funext x
  show sInf _ = sInf _
  congr 1
  ext n
  exact ⟨fun ⟨E, ⟨f⟩, h⟩ => ⟨E, ⟨f ≪≫ e⟩, h⟩, fun ⟨E, ⟨f⟩, h⟩ => ⟨E, ⟨f ≪≫ e.symm⟩, h⟩⟩

section OpenImmersion

variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]

/-- The derived stalk of a complex depends only on its class in the derived category. -/
theorem nonempty_derivedStalkOfComplex_iso_of_iso [HasDerivedCategory.{w} X.Modules] (x : X)
    {E₁ E₂ : CochainComplex X.Modules ℤ}
    (e : DerivedCategory.Q.obj E₁ ≅ DerivedCategory.Q.obj E₂) :
    Nonempty (derivedStalkOfComplex x E₁ ≅ derivedStalkOfComplex x E₂) :=
  ⟨((modulesStalkFunctor x).mapDerivedCategoryFactors.app E₁).symm ≪≫
    (modulesStalkFunctor x).mapDerivedCategory.mapIso e ≪≫
      (modulesStalkFunctor x).mapDerivedCategoryFactors.app E₂⟩

/-- The degreewise restriction of a complex along `j`. -/
abbrev restrictComplex (E : CochainComplex X.Modules ℤ) : CochainComplex Y.Modules ℤ :=
  ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj E

/-- **The stalk of a restricted complex.** The derived stalk of `E` at `j y` is the restriction of
scalars along the stalk map of the derived stalk of `E|_Y` at `y`. -/
theorem nonempty_derivedStalkOfComplex_iso_restrictScalars (y : Y)
    (E : CochainComplex X.Modules ℤ) :
    Nonempty (derivedStalkOfComplex (j y) E ≅
      (ModuleCat.restrictScalars.{u} (j.stalkMap y).hom).mapDerivedCategory.obj
        (derivedStalkOfComplex y (restrictComplex j E))) := by
  let R := ModuleCat.restrictScalars.{u} (j.stalkMap y).hom
  have eC : ((modulesStalkFunctor (j y)).mapHomologicalComplex (ComplexShape.up ℤ)).obj E ≅
      (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((modulesStalkFunctor y).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (restrictComplex j E)) :=
    (NatIso.mapHomologicalComplex (restrictStalkModuleNatIso j y) (ComplexShape.up ℤ)).symm.app E
  exact ⟨DerivedCategory.Q.mapIso eC ≪≫ (R.mapDerivedCategoryFactors.app _).symm⟩

variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- **Normalization of a stalk is local.** For an open immersion `j : Y ⟶ X`, a complex `E` on
`X`, `y ∈ Y` and `n ∈ ℤ`, the shifted derived stalk of `E|_Y` at `y` is a normalized dualizing
complex over `𝒪_{Y,y}` exactly when the shifted derived stalk of `E` at `j y` is one over
`𝒪_{X,j y}`. -/
theorem isNormalizedDualizingComplex_derivedStalkOfComplex_restrict_iff (y : Y)
    (E : CochainComplex X.Modules ℤ) (n : ℤ) :
    Dualizing.IsNormalizedDualizingComplex.{u, u}
        ((derivedStalkOfComplex y (restrictComplex j E))⟦-n⟧) ↔
      Dualizing.IsNormalizedDualizingComplex.{u, u} ((derivedStalkOfComplex (j y) E)⟦-n⟧) := by
  have := isIso_stalkMap_of_isOpenImmersion j y
  have hbij : Function.Bijective (j.stalkMap y).hom :=
    ConcreteCategory.bijective_of_isIso (j.stalkMap y)
  let R := ModuleCat.restrictScalars.{u} (j.stalkMap y).hom
  obtain ⟨e⟩ := nonempty_derivedStalkOfComplex_iso_restrictScalars j y E
  have eS : (derivedStalkOfComplex (j y) E)⟦-n⟧ ≅
      R.mapDerivedCategory.obj ((derivedStalkOfComplex y (restrictComplex j E))⟦-n⟧) :=
    (shiftFunctor _ (-n)).mapIso e ≪≫ ((R.mapDerivedCategory.commShiftIso (-n)).app _).symm
  refine ⟨fun h => (Dualizing.isNormalizedDualizingComplex_congr.{u, u} eS).mpr
    (Dualizing.isNormalizedDualizingComplex_restrictScalars_of_bijective _ hbij _ h), fun h => ?_⟩
  let ψ : X.presheaf.stalk (j y) ≃+* Y.presheaf.stalk y := RingEquiv.ofBijective _ hbij
  let R' := ModuleCat.restrictScalars.{u} ψ.symm.toRingHom
  have h' := Dualizing.isNormalizedDualizingComplex_restrictScalars_of_bijective
    ψ.symm.toRingHom ψ.symm.bijective _ ((Dualizing.isNormalizedDualizingComplex_congr.{u, u}
      eS).mp h)
  have eId : R ⋙ R' ≅ 𝟭 _ :=
    (ModuleCat.restrictScalarsComp' ψ.symm.toRingHom (j.stalkMap y).hom (RingHom.id _)
      (by ext a; exact (ψ.apply_symm_apply a).symm)).symm ≪≫ ModuleCat.restrictScalarsId _
  refine (Dualizing.isNormalizedDualizingComplex_congr.{u, u} ?_).mp h'
  exact (mapDerivedCategoryCompIso R R').symm.app _ ≪≫
    (mapDerivedCategoryIsoOfNatIso _ _ eId).app _ ≪≫
      Stacks.Homology.mapDerivedCategoryIdIso.app _

/-- **The dimension function is local** ([Stacks, Tag 0AWF]): for an open immersion
`j : Y ⟶ X` and `K ∈ D(𝒪_X)`, the function `δ` of `K|_Y` at `y` is that of `K` at `j y`. -/
theorem associatedShiftFunction_restrict_of_isOpenImmersion [HasDerivedCategory.{w} X.Modules]
    [HasDerivedCategory.{w'} Y.Modules] (K : DerivedCategory X.Modules) (y : Y) :
    associatedShiftFunction ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj K) y =
      associatedShiftFunction K (j y) := by
  let E₀ := DerivedCategory.Q.objPreimage K
  have hE₀ : DerivedCategory.Q.obj E₀ ≅ K := DerivedCategory.Q.objObjPreimageIso K
  have hr : ∀ E : CochainComplex X.Modules ℤ, Nonempty (DerivedCategory.Q.obj E ≅ K) →
      Nonempty (DerivedCategory.Q.obj (restrictComplex j E) ≅
        (Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj K) := fun E ⟨e⟩ =>
    ⟨((Scheme.Modules.restrictFunctor j).mapDerivedCategoryFactors.app E).symm ≪≫
      (Scheme.Modules.restrictFunctor j).mapDerivedCategory.mapIso e⟩
  show sInf _ = sInf _
  congr 1
  ext n
  refine ⟨fun ⟨E, ⟨e⟩, h⟩ => ?_, fun ⟨E, hE, h⟩ => ⟨restrictComplex j E, hr E hE,
    (isNormalizedDualizingComplex_derivedStalkOfComplex_restrict_iff j y E n).mpr h⟩⟩
  obtain ⟨e₀⟩ := hr E₀ ⟨hE₀⟩
  obtain ⟨s⟩ := nonempty_derivedStalkOfComplex_iso_of_iso y (e ≪≫ e₀.symm)
  exact ⟨E₀, ⟨hE₀⟩, (isNormalizedDualizingComplex_derivedStalkOfComplex_restrict_iff j y E₀ n).mp
    ((Dualizing.isNormalizedDualizingComplex_congr.{u, u} ((shiftFunctor _ (-n)).mapIso s)).mp h)⟩

end OpenImmersion

end Stacks.Duality

end

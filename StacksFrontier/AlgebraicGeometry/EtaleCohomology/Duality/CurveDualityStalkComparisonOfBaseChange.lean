module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ProperCurveRelativeDualityAssembly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveDualityMapBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusTwistStalk

/-!
# The duality map of a relative curve at the geometric fibres

Let `f : X ⟶ S` be a smooth projective curve as in
`Stacks.EtaleCohomology.ProperCurveRelativeDualityInput`, `ℓ` a prime and `Λ = ℤ/ℓ`. For a
geometric point `x̄ : Spec Ω ⟶ S` with fibre `f' : X_{x̄} ⟶ Spec Ω`, the inverse image along `x̄`
of the duality map `D_{m,t}` of `f` is invertible as soon as the duality map `D_{m',t'}` of the
fibre (for the induced multiplication and trace) and the comparison
`x̄⁻¹ RHom(K, Λ_S[-2]) ⟶ RHom(x̄⁻¹K, x̄⁻¹Λ_S[-2])` of [Stacks, Tag 08JF] are
(`Stacks.EtaleCohomology.isIso_etaleModuleDerivedInverseImage_map_curveDualityMap`). Since the
derived stalk at `x̄` is invertible once the inverse image along `x̄` is,
`Stacks.EtaleCohomology.CurveDualityStalkComparison`, and hence relative duality for a smooth
projective curve, follows from the invertibility of the comparison of Tag 08JF at the geometric
points.

## Main definitions

* `Stacks.EtaleCohomology.CurveDualityHomComparisonIso`: the comparison of Tag 08JF is invertible
  at every geometric point.

## Main results

* `Stacks.EtaleCohomology.isIso_smallEtaleDerivedStalkAb_of_isIso_inverseImage`: the derived
  stalk at a geometric point is invertible once the derived inverse image along it is.
* `Stacks.EtaleCohomology.curveDualityStalkComparison_of_curveDualityHomComparisonIso`:
  `CurveDualityStalkComparison` from `CurveDualityHomComparisonIso`.
* `Stacks.EtaleCohomology.properCurveRelativeDualityInput_of_curveDualityHomComparisonIso`:
  relative duality for a smooth projective curve from `CurveDualityHomComparisonIso`.

## Implementation notes

The derived categories are those of the standard model `HasDerivedCategory.standard`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.Prod
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

open Stacks.EtaleCohomology.ExtensionTorsor

section Stalk

variable {Λ : Type} [CommRing Λ] {S : Scheme.{u}}

/-- The stalk of the underlying abelian sheaf at a geometric point `x̄` is the stalk at the
identity of `Spec Ω` of the underlying abelian sheaf of `x̄⁻¹`. -/
def etaleModuleUnderlyingAbelianStalkInverseImageIso (x : GeometricPoint S) :
    etaleModuleUnderlyingAbelian S Λ ⋙ smallEtaleStalkAb (𝟙 _ ≫ x.hom) ≅
      etaleModuleInverseImage.{u, 0} Λ x.hom ⋙
        etaleModuleUnderlyingAbelian (Spec (.of x.residueField)) Λ ⋙ smallEtaleStalkAb (𝟙 _) :=
  (Scheme.pointSmallEtale (𝟙 _ ≫ x.hom)).sheafFiberCompIso
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≪≫
    Functor.isoWhiskerRight (etaleModuleStalkPullbackIso.{u, 0} Λ x.hom (𝟙 _)).symm
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (etaleModuleInverseImage.{u, 0} Λ x.hom)
      ((Scheme.pointSmallEtale (𝟙 (Spec (.of x.residueField)))).sheafFiberCompIso
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).symm

/-- A morphism of sheaves of `Λ`-modules whose inverse image along a geometric point `x̄` is
invertible has an invertible stalk at `x̄`. -/
theorem isIso_smallEtaleStalkAb_map_of_isIso_inverseImage (x : GeometricPoint S)
    {F F' : EtaleModules.{u, 0} Λ S} (ψ : F ⟶ F')
    (h : IsIso ((etaleModuleInverseImage.{u, 0} Λ x.hom).map ψ)) :
    IsIso ((smallEtaleStalkAb x.hom).map ((etaleModuleUnderlyingAbelian S Λ).map ψ)) := by
  have h' : IsIso ((etaleModuleUnderlyingAbelian S Λ ⋙ smallEtaleStalkAb (𝟙 _ ≫ x.hom)).map ψ) :=
    (NatIso.isIso_map_iff (etaleModuleUnderlyingAbelianStalkInverseImageIso x) ψ).2
      (by dsimp only [Functor.comp_map]; infer_instance)
  rwa [Category.id_comp] at h'

/-- Applying a functor `G` to the homology of `F.mapDerivedCategory.map φ` is invertible iff it is
for `F` applied to the homology of `φ`. -/
private theorem isIso_map_homologyFunctor_map_mapDerivedCategory_iff
    {C D E : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D] [Category E]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : D ⥤ E) (n : ℤ) {M N : DerivedCategory C} (φ : M ⟶ N) :
    IsIso (G.map ((DerivedCategory.homologyFunctor D n).map (F.mapDerivedCategory.map φ))) ↔
      IsIso (G.map (F.map ((DerivedCategory.homologyFunctor C n).map φ))) :=
  NatIso.isIso_map_iff (Functor.isoWhiskerRight
    (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso F n) G) φ

/-- **The derived stalk at a geometric point `x̄` is invertible once the derived inverse image
along `x̄` is.** -/
theorem isIso_smallEtaleDerivedStalkAb_of_isIso_inverseImage (x : GeometricPoint S)
    {M N : DerivedCategory (EtaleModules.{u, 0} Λ S)} (φ : M ⟶ N)
    (h : IsIso ((etaleModuleDerivedInverseImage.{u, 0} Λ x.hom).map φ)) :
    IsIso ((smallEtaleDerivedStalkAb x.hom).map
      ((etaleModuleUnderlyingAbelian S Λ).mapDerivedCategory.map φ)) := by
  rw [DerivedCategory.isIso_iff]
  intro n
  have hn : IsIso ((etaleModuleInverseImage.{u, 0} Λ x.hom).map
      ((DerivedCategory.homologyFunctor _ n).map φ)) :=
    (isIso_map_homologyFunctor_map_mapDerivedCategory_iff _ (𝟭 _) n φ).1
      (Functor.map_isIso (DerivedCategory.homologyFunctor _ n) _)
  have hs := isIso_smallEtaleStalkAb_map_of_isIso_inverseImage x _ hn
  refine (isIso_map_homologyFunctor_map_mapDerivedCategory_iff _ (𝟭 _) n _).2 ?_
  exact (isIso_map_homologyFunctor_map_mapDerivedCategory_iff _ (smallEtaleStalkAb x.hom) n φ).2 hs

end Stalk

section Assembly

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **The comparison of Tag 08JF at the geometric points**: in the setting of
`Stacks.EtaleCohomology.ProperCurveRelativeDualityInput`, for every geometric point
`x̄ : Spec Ω ⟶ S` the comparison
`x̄⁻¹ RHom(Rf_* E, Λ_S[-2]) ⟶ RHom(x̄⁻¹ Rf_* E, x̄⁻¹ Λ_S[-2])` is invertible. -/
def CurveDualityHomComparisonIso : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k], IsUnit (ℓ : k) →
    ∀ (S X : Scheme.{u}) (q : S ⟶ Spec (.of k)) (e : ℕ) [SmoothOfRelativeDimension e q]
      [IsAffine S] (f : X ⟶ S) [SmoothOfRelativeDimension 1 f] [GeometricallyIrreducible f],
      IsProjectiveMorphism f → ∀ x : GeometricPoint S,
        IsIso (etaleDerivedInverseImageHomComparison.{u, 0} (ZMod ℓ) x.hom (curveDualityComplex ℓ f)
          (((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ))⟦(-2 : ℤ)⟧))

/-- **The duality map is compatible with the geometric fibres**, granted the comparison of
Tag 08JF at the geometric points. -/
theorem curveDualityStalkComparison_of_curveDualityHomComparisonIso
    (hC : CurveDualityHomComparisonIso.{u} ℓ) : CurveDualityStalkComparison.{u} ℓ := by
  intro k _ _ hℓ S X q e _ _ f _ _ hf t ht x
  have := isProper_of_isProjectiveMorphism f hf
  have sq := IsPullback.of_hasPullback f x.hom
  exact ⟨curveDualityBaseChangeMultiplication ℓ f x.hom (pullback.snd f x.hom)
      (pullback.fst f x.hom) sq.w (curveDualityMultiplication ℓ f),
    isIso_curveDualityBaseChangeMultiplication ℓ f x.hom _ _ sq.w _,
    curveDualityBaseChangeTrace ℓ f x.hom _ _ sq t,
    isIso_homologyFunctor_map_curveDualityBaseChangeTrace ℓ f x.hom _ _ sq t ht, fun hD =>
      isIso_smallEtaleDerivedStalkAb_of_isIso_inverseImage x _
        (isIso_etaleModuleDerivedInverseImage_map_curveDualityMap ℓ f x.hom _ _ sq _ t
          (hC k hℓ S X q e f hf x) hD)⟩

/-- **Relative Poincaré duality for a smooth projective curve**
(`Stacks.EtaleCohomology.ProperCurveRelativeDualityInput`), granted the comparison of Tag 08JF
at the geometric points. -/
theorem properCurveRelativeDualityInput_of_curveDualityHomComparisonIso
    (hC : CurveDualityHomComparisonIso.{u} ℓ) (k : Type u) [Field k] [IsAlgClosed k] :
    ProperCurveRelativeDualityInput ℓ k :=
  properCurveRelativeDualityInput_of_curveDualityStalkComparison ℓ
    (curveDualityStalkComparison_of_curveDualityHomComparisonIso ℓ hC) k

end Assembly

end Stacks.EtaleCohomology

end

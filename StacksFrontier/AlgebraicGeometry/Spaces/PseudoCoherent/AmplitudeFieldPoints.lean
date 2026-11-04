module

public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.AffineChartModelBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedFibreBettiNumbers
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativelyPerfectClosedFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.PrimeResidueFieldSite
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageUniformBound
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSchemeComparison
public import StacksFrontier.Algebra.Homology.TopHomologyResidueFields
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped

/-!
# The cohomological amplitude of a pseudo-coherent complex is detected at field points

Let `Y` be a quasi-compact algebraic space and `E ∈ D(𝒪_Y)` pseudo-coherent. If the derived
fibre `Ly^*E` lies in `D^{≤ a}` at every field-valued point `y : Spec k ⟶ Y`, then `E` lies in
`D^{≤ a}`. This is the derived Nakayama lemma (Stacks 068V) for algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.isZero_homology_of_isZero_homology_chartModel`: `ε^*((-)~)` reflects
  vanishing of cohomology.
* `AlgebraicGeometry.Space.isLE_etaleModulePullback_of_forall_fieldValuedPoint_isLE`: the
  amplitude of a pseudo-coherent complex on an affine étale chart is detected at field points.
* `AlgebraicGeometry.Space.isLE_of_isPseudoCoherent_of_forall_fieldValuedPoint_isLE`: the
  amplitude of a pseudo-coherent complex on a quasi-compact algebraic space is detected at field
  points.

## References

* [Stacks Project, Tag 068V](https://stacks.math.columbia.edu/tag/068V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

open scoped Stacks.StandardDerivedModel

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section ChartModel

private theorem isQuasicoherent_tilde_functor_obj (R : CommRingCat.{u}) (M : ModuleCat.{u} R) :
    ((tilde.functor R).obj M).IsQuasicoherent :=
  inferInstance

private theorem isZero_tilde_functor_obj_iff (R : CommRingCat.{u}) (M : ModuleCat.{u} R) :
    IsZero ((tilde.functor R).obj M) ↔ IsZero M :=
  ⟨fun h => IsZero.of_full_of_faithful_of_isZero (tilde.functor R) _ h,
    fun h => Functor.map_isZero _ h⟩

variable {A : Type u} [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
  (g : B.obj hA ⟶ B.obj hS)

/-- The cohomology of the chart model `ε^*(P~)` is `ε^*` of the sheaf associated with the
cohomology of `P`. -/
def homologyChartModelIso (P : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    (DerivedCategory.homologyFunctor _ i).obj
      ((representedDerivedAssociatedModule B S hS (specFppfOver B S hS hA g)).obj
        ((tilde.functor (CommRingCat.of A) ⋙ Scheme.Modules.restrictFunctor
          (Iso.refl ((BigFppfOver.toScheme B S hS).obj
            (specFppfOver B S hS hA g))).hom).mapDerivedCategory.obj (DerivedCategory.Q.obj P))) ≅
      (representedAssociatedModule B S hS (specFppfOver B S hS hA g)
        (isAlgebraicSpace_yoneda B S hS _)).obj
        ((tilde.functor (CommRingCat.of A)).obj (P.homology i)) :=
  haveI := AlgebraicGeometry.tilde.preservesFiniteLimits (CommRingCat.of A)
  let G := representedAssociatedModule B S hS (specFppfOver B S hS hA g)
    (isAlgebraicSpace_yoneda B S hS _)
  let eX := chartModelTildeIso B S hS hA g P ≪≫
    ((tilde.functor (CommRingCat.of A)).mapDerivedCategoryFactors.app P).symm
  (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso G i).app _ ≪≫
    G.mapIso ((DerivedCategory.homologyFunctor _ i).mapIso eX ≪≫
      (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
        (tilde.functor (CommRingCat.of A)) i).app _ ≪≫
      (tilde.functor (CommRingCat.of A)).mapIso
        ((DerivedCategory.homologyFunctorFactors _ i).app P))

/-- **`ε^*((-)~)` reflects vanishing of cohomology.** If the `i`-th cohomology sheaf of the chart
model `ε^*(P~)` on `h_{Spec A}` vanishes, then `H^i(P) = 0`. -/
theorem isZero_homology_of_isZero_homology_chartModel (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((representedDerivedAssociatedModule B S hS (specFppfOver B S hS hA g)).obj
        ((tilde.functor (CommRingCat.of A) ⋙ Scheme.Modules.restrictFunctor
          (Iso.refl ((BigFppfOver.toScheme B S hS).obj
            (specFppfOver B S hS hA g))).hom).mapDerivedCategory.obj (DerivedCategory.Q.obj P))))) :
    IsZero (P.homology i) :=
  (isZero_tilde_functor_obj_iff _ _).1 <|
    isZero_of_isZero_representedAssociatedModule B S hS (specFppfOver B S hS hA g)
      (isAlgebraicSpace_yoneda B S hS _) _ (isQuasicoherent_tilde_functor_obj _ _)
      (h.of_iso (homologyChartModelIso hA g P i).symm)

/-- **`ε^*((-)~)` preserves vanishing of cohomology.** -/
theorem isZero_homology_chartModel_of_isZero_homology (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (i : ℤ) (h : IsZero (P.homology i)) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((representedDerivedAssociatedModule B S hS (specFppfOver B S hS hA g)).obj
        ((tilde.functor (CommRingCat.of A) ⋙ Scheme.Modules.restrictFunctor
          (Iso.refl ((BigFppfOver.toScheme B S hS).obj
            (specFppfOver B S hS hA g))).hom).mapDerivedCategory.obj
          (DerivedCategory.Q.obj P)))) := by
  have := additive_representedAssociatedModule B S hS (specFppfOver B S hS hA g)
    (isAlgebraicSpace_yoneda B S hS _)
  refine IsZero.of_iso ?_ (homologyChartModelIso hA g P i)
  exact Functor.map_isZero _ ((isZero_tilde_functor_obj_iff _ _).2 h)

end ChartModel

/-! ### The amplitude on an affine étale chart -/

variable {Y : AlgebraicSpaces B S hS}

/-- If `X ∈ D^{≤ a}` and vanishing of `Hⁱ X` forces vanishing of `Hⁱ Z`, then `Z ∈ D^{≤ a}`. -/
private theorem isLE_of_isLE_of_isZero_homology_imp {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    {X : DerivedCategory C} {Z : DerivedCategory D} {a : ℤ} (hX : X.IsLE a)
    (h : ∀ i, IsZero ((DerivedCategory.homologyFunctor _ i).obj X) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj Z)) : Z.IsLE a :=
  (DerivedCategory.isLE_iff _ a).2 fun i hi ↦ h i ((DerivedCategory.isLE_iff _ a).1 hX i hi)

/-- **The amplitude of a pseudo-coherent complex on an affine étale chart is detected at field
points.** Let `φ : h_{Spec A} ⟶ Y` be étale and `E ∈ D(𝒪_Y)` pseudo-coherent with
`Ly^*E ∈ D^{≤ a}` at every field-valued point `y` of `Y`. Then `φ^*E ∈ D^{≤ a}`. -/
theorem isLE_etaleModulePullback_of_forall_fieldValuedPoint_isLE {A : Type u} [CommRing A]
    (hA : B.Contains (Spec (CommRingCat.of A))) (g : B.obj hA ⟶ B.obj hS)
    (φ : (schemeSpace (specFppfOver B S hS hA g) :
      AlgebraicSpaces B S hS) ⟶ Y) (hφ : IsEtale B S hS φ.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (hE : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent E) (a : ℤ)
    (h : ∀ p : FieldValuedPoint B S hS Y.1,
      ((smallEtaleDerivedModulePullback B S hS p.toSpace).obj E).IsLE a) :
    letI := etaleModulePullback_additive.{u, u} B S hS φ hφ
    letI := preservesFiniteLimits_etaleModulePullback B S hS φ hφ
    letI := preservesFiniteColimits_etaleModulePullback B S hS φ hφ
    ((etaleModulePullback.{u, u} B S hS φ hφ).mapDerivedCategory.obj E).IsLE a := by
  let := etaleModulePullback_additive.{u, u} B S hS φ hφ
  let := preservesFiniteLimits_etaleModulePullback B S hS φ hφ
  let := preservesFiniteColimits_etaleModulePullback B S hS φ hφ
  obtain ⟨P, hP, ⟨eP⟩⟩ := exists_isBoundedAboveFiniteFree_etaleModulePullback_iso B S hS hA g φ hφ
    E hE
  have hfib : ∀ p : PrimeSpectrum A, ∀ i : ℤ, a < i →
      IsZero (((CochainComplex.extendScalars
        (algebraMap A p.asIdeal.ResidueField)).obj P).homology i) := by
    intro p i hi
    let κ := p.asIdeal.ResidueField
    have hκ : B.Contains (Spec (CommRingCat.of κ)) :=
      BigFppfSite.contains_spec_residueField_atPrime B hA p.asIdeal
    let gκ : B.obj hκ ⟶ B.obj hS :=
      (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap A κ))) :
        B.obj hκ ⟶ B.obj hA) ≫ g
    let j := specFppfOverMap B S hS hA g hκ gκ rfl
    have := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS
      (representedSpaceMap B S hS j)
    obtain ⟨e₆⟩ := nonempty_smallEtaleDerivedModulePullback_chartModel_iso B S hS hA g hκ gκ rfl
      P hP
    obtain ⟨e₅⟩ := nonempty_etaleModulePullback_mapDerivedCategory_iso φ hφ E
    let r : FieldValuedPoint B S hS (yoneda.obj (specFppfOver B S hS hA g)) :=
      ⟨κ, hκ, gκ.hom, j⟩
    have hr : FieldValuedPoint.toSpace (Y := schemeSpace (specFppfOver B S hS hA g)) r =
        representedSpaceMap B S hS j :=
      ObjectProperty.hom_ext _ (yonedaEquiv.symm_apply_eq.2 (yonedaEquiv_yoneda_map j).symm)
    have ht : (r.map B S hS _ φ.hom).toSpace = representedSpaceMap B S hS j ≫ φ := by
      rw [FieldValuedPoint.toSpace_map (Y := Y) φ r, hr]
      rfl
    have := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS φ
    have := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS
      (representedSpaceMap B S hS j ≫ φ)
    have hLE := h (r.map B S hS _ φ.hom)
    rw [ht] at hLE
    let e : (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS j ≫ φ)).obj E ≅
        _ := ((smallEtaleDerivedPullbackCompIsoOfTwoIso B S hS (representedSpaceMap B S hS j)
          φ).app E).symm ≪≫
        (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS j)).mapIso
          (e₅.symm ≪≫ eP) ≪≫ e₆
    exact isZero_homology_of_isZero_homology_chartModel hκ gκ _ i
      (((DerivedCategory.isLE_iff _ a).1 hLE i hi).of_iso
        ((DerivedCategory.homologyFunctor _ i).mapIso e.symm))
  have hPLE : (DerivedCategory.Q.obj P).IsLE a := (DerivedCategory.isLE_iff _ a).2 fun i hi ↦
    open StacksDraft.PseudoCoherence in
    (isZero_homology_of_forall_isZero_homology_extendScalars_residueField_of_lt
      P hP a hfib i hi).of_iso ((DerivedCategory.homologyFunctorFactors _ i).app P)
  have hmodel := isLE_of_isLE_of_isZero_homology_imp (Z := (representedDerivedAssociatedModule B S
      hS (specFppfOver B S hS hA g)).obj ((tilde.functor (CommRingCat.of A) ⋙
        Scheme.Modules.restrictFunctor (Iso.refl ((BigFppfOver.toScheme B S hS).obj
          (specFppfOver B S hS hA g))).hom).mapDerivedCategory.obj (DerivedCategory.Q.obj P)))
    hPLE fun i hi ↦ isZero_homology_chartModel_of_isZero_homology hA g P i
      (hi.of_iso ((DerivedCategory.homologyFunctorFactors _ i).app P).symm)
  exact DerivedCategory.TStructure.t.isLE_of_iso eP.symm a

/-- **The cohomological amplitude of a pseudo-coherent complex on a quasi-compact algebraic space
is detected at its field points** (the derived Nakayama lemma, Stacks 068V, on spaces). Let `Y`
be a quasi-compact algebraic space and `E ∈ D(𝒪_Y)` pseudo-coherent such that the derived fibre
`Ly^*E` lies in `D^{≤ a}` for every field-valued point `y : Spec k ⟶ Y`. Then `E ∈ D^{≤ a}`. -/
theorem isLE_of_isPseudoCoherent_of_forall_fieldValuedPoint_isLE (Y : AlgebraicSpaces B S hS)
    (hqc : IsQuasiCompactSpace B S hS Y.1)
    (E : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (hE : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent E) (a : ℤ)
    (h : ∀ p : FieldValuedPoint B S hS Y.1,
      ((smallEtaleDerivedModulePullback B S hS p.toSpace).obj E).IsLE a) :
    E.IsLE a := by
  obtain ⟨A, _, hA, g, φ, hφ, hφs⟩ := exists_specFppfOver_surjective_etale_chart B S hS Y hqc
  let := etaleModulePullback_additive.{u, u} B S hS φ hφ
  let := preservesFiniteLimits_etaleModulePullback B S hS φ hφ
  let := preservesFiniteColimits_etaleModulePullback B S hS φ hφ
  have hchart := isLE_etaleModulePullback_of_forall_fieldValuedPoint_isLE hA g φ hφ E hE a h
  exact isLE_of_isLE_of_isZero_homology_imp hchart fun i hi ↦
    isZero_of_isZero_etaleModulePullback_of_isSurjective B S hS φ hφ hφs _ <|
      hi.of_iso
        ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
          (etaleModulePullback.{u, u} B S hS φ hφ) i).app E).symm

end AlgebraicGeometry.Space

end

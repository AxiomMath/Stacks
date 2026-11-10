module

public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTopDegree
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapLocal
public import StacksFrontier.RingTheory.MilnorPatching.ModuleCategory

/-!
# The unit of derived base change in the top degree, along a surjection

Let `f : R →+* R₀` be a surjective map of commutative rings, with kernel `I`, and let `M` be an
object of `D(R)` with no cohomology in positive degrees. The top-degree comparison
`R₀ ⊗_R H⁰(M) ≅ H⁰(M ⊗^𝐋_R R₀)` (`StacksDraft.TopDegreeExtendScalars.isIso_topDegreeComparison`,
right exactness) shows that the map induced on `H⁰` by the unit `M ⟶ (M ⊗^𝐋_R R₀)|_R` of derived
extension and restriction of scalars is, up to that isomorphism, `m ↦ 1 ⊗ m`. Since `f` is
surjective, it is therefore surjective with kernel `I • H⁰(M)`.

## Main results

* `StacksDraft.TopDegreeExtendScalars.surjective_homology_unit`.
* `StacksDraft.TopDegreeExtendScalars.ker_homology_unit`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace StacksDraft.TopDegreeExtendScalars

variable {R R₀ : Type u} [CommRing R] [CommRing R₀] (f : R →+* R₀)
  (M : DerivedCategory (ModuleCat.{u} R))

/-- The map induced on `H⁰` by the unit of derived extension and restriction of scalars, followed
by the identification of `H⁰` of a restriction of scalars, is the unit of extension and restriction
of scalars on `H⁰` followed by the restriction of the top-degree comparison. -/
theorem homology_unit_comp_eq :
    (DerivedCategory.homologyFunctor _ 0).map
        ((RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction f).unit.app M) ≫
      ((ModuleCat.restrictScalars f).mapDerivedCategoryHomologyIso 0).hom.app _ =
    (ModuleCat.extendRestrictScalarsAdj f).unit.app _ ≫
      (ModuleCat.restrictScalars f).map (topDegreeComparison f M 0) :=
  (((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).apply_symm_apply _).symm.trans
    (Adjunction.homEquiv_unit _ _ _ (topDegreeComparison f M 0))

variable [M.IsLE 0]

/-- **The unit is surjective on `H⁰`** along a surjective ring map, for `M` with no cohomology in
positive degrees. -/
theorem surjective_homology_unit (hf : Function.Surjective f) :
    Function.Surjective ((DerivedCategory.homologyFunctor _ 0).map
      ((RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction f).unit.app M)) := by
  let : Algebra R R₀ := f.toAlgebra
  have := isIso_topDegreeComparison f M 0
  have hι := ConcreteCategory.bijective_of_isIso
    (((ModuleCat.restrictScalars f).mapDerivedCategoryHomologyIso 0).hom.app
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        f).functor.obj M))
  have hc := ConcreteCategory.bijective_of_isIso
    ((ModuleCat.restrictScalars f).map (topDegreeComparison f M 0))
  have hu₀ : Function.Surjective (TensorProduct.mk R R₀
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj M) 1) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul r m =>
      obtain ⟨a, rfl⟩ := hf r
      refine ⟨a • m, ?_⟩
      rw [TensorProduct.mk_apply, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
      rfl
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add _ _ _⟩
  have hu : Function.Surjective ((ModuleCat.extendRestrictScalarsAdj f).unit.app
      ((DerivedCategory.homologyFunctor _ 0).obj M)) := hu₀
  intro y
  obtain ⟨z, hz⟩ := (hc.2.comp hu) (((ModuleCat.restrictScalars f).mapDerivedCategoryHomologyIso
    0).hom.app _ y)
  refine ⟨z, hι.1 ?_⟩
  have := congrArg (fun φ => φ z) (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _))
    (homology_unit_comp_eq f M))
  simp only [ConcreteCategory.comp_apply] at this
  exact this.trans hz

/-- **The kernel of the unit on `H⁰`** along a surjective ring map `f` is `ker f • H⁰(M)`, for `M`
with no cohomology in positive degrees. -/
theorem ker_homology_unit (hf : Function.Surjective f) :
    LinearMap.ker ((DerivedCategory.homologyFunctor _ 0).map
      ((RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction f).unit.app M)).hom =
      RingHom.ker f • ⊤ := by
  let : Algebra R R₀ := f.toAlgebra
  have := isIso_topDegreeComparison f M 0
  have hι := ConcreteCategory.bijective_of_isIso
    (((ModuleCat.restrictScalars f).mapDerivedCategoryHomologyIso 0).hom.app
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        f).functor.obj M))
  have hc := ConcreteCategory.bijective_of_isIso
    ((ModuleCat.restrictScalars f).map (topDegreeComparison f M 0))
  rw [← MilnorPatching.ker_tensorProductMk_of_surjective f hf]
  ext x
  simp only [LinearMap.mem_ker]
  have := congrArg (fun φ => φ x) (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _))
    (homology_unit_comp_eq f M))
  simp only [ConcreteCategory.comp_apply] at this
  refine ⟨fun hx => (hc.1.eq_iff' (map_zero _)).mp <| this.symm.trans <|
      (congrArg (ConcreteCategory.hom
        (((ModuleCat.restrictScalars f).mapDerivedCategoryHomologyIso 0).hom.app
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            f).functor.obj M))) hx).trans (map_zero _),
    fun hx => (hι.1.eq_iff' (map_zero _)).mp <| this.trans <|
      (congrArg (ConcreteCategory.hom
        ((ModuleCat.restrictScalars f).map (topDegreeComparison f M 0))) hx).trans (map_zero _)⟩

end StacksDraft.TopDegreeExtendScalars

end

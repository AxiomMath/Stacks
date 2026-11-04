module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapTensor
public import StacksFrontier.Homology.KFlat.Flat

/-!
# The comparison of Stacks 065Z at a complex flat over the base

Let `R → A`, `R → R'`, `A → A'`, `R' → A'` be a cocartesian square of commutative rings, so that
`A' = A ⊗_R R'`, and let `N` be a bounded above complex of `A`-modules whose terms are flat over
`R`. Then the comparison `N ⊗ᴸ_R R' ⟶ N ⊗ᴸ_A A'` of Stacks 065Z followed by the comparison
`N ⊗ᴸ_A A' ⟶ N ⊗_A A'` with the termwise tensor product is an isomorphism: the complex `N` is
K-flat over `R`, so `N ⊗ᴸ_R R' = N ⊗_R R'`, and `N ⊗_R R' = N ⊗_A A'` termwise.

## Main results

* `RingTheory.TorIndependence.isIso_underivedSquareComparison_app_of_isPushout`: the termwise
  comparison `R' ⊗_R M ⟶ A' ⊗_A M` of a cocartesian square is bijective.
* `RingTheory.TorIndependence.isIso_ringHomSquareComparison_comp_comparison_of_flat`: for a
  bounded above complex `N` with terms flat over `R`, the comparison `N ⊗ᴸ_R R' ⟶ N ⊗ᴸ_A A'` of
  Stacks 065Z followed by `N ⊗ᴸ_A A' ⟶ N ⊗_A A'` is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace RingTheory.TorIndependence

attribute [local instance] HasDerivedCategory.standard

variable {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  (f : R →+* A) (g : R →+* R') (h : A →+* A') (i : R' →+* A') (sq : h.comp f = i.comp g)

/-- **The termwise comparison of a cocartesian square is bijective.** For a pushout square of
commutative rings, `R' ⊗_R M ⟶ A' ⊗_A M`, `r' ⊗ m ↦ i(r') ⊗ m`, is an isomorphism for every
`A`-module `M`. -/
theorem isIso_underivedSquareComparison_app_of_isPushout
    (hpo : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g) (CommRingCat.ofHom h)
      (CommRingCat.ofHom i)) (M : ModuleCat.{u} A) :
    IsIso ((underivedSquareComparison f g h i sq).app M) := by
  let : Algebra R A := f.toAlgebra
  let : Algebra R R' := g.toAlgebra
  let : Algebra A A' := h.toAlgebra
  let : Algebra R' A' := i.toAlgebra
  let : Algebra R A' := (i.comp g).toAlgebra
  have : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq' sq.symm
  have : IsScalarTower R R' A' := IsScalarTower.of_algebraMap_eq' rfl
  let : Module R M := Module.compHom M f
  have : IsScalarTower R A M := ⟨fun r a m => mul_smul (f r) a m⟩
  have : Algebra.IsPushout R R' A A' := ((CommRingCat.isPushout_iff_isPushout).1 hpo).symm
  let e := Algebra.IsPushout.cancelBaseChange R R' A A' M
  have he : ∀ x, ((underivedSquareComparison f g h i sq).app M).hom x = e.symm x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | tmul r' m =>
      exact (underivedSquareComparison_app_tmul f g h i sq M r' m).trans
        (Algebra.IsPushout.cancelBaseChange_symm_tmul R R' A A' M r' m).symm
    | add x y hx hy =>
      exact (map_add ((underivedSquareComparison f g h i sq).app M).hom x y).trans
        ((congrArg₂ (· + ·) hx hy).trans (map_add e.symm x y).symm)
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (((underivedSquareComparison f g h i sq).app M).hom : _ → _)
  exact (funext he).symm ▸ e.symm.bijective

/-- **Stacks 065Z at a complex flat over the base.** For a cocartesian square of commutative
rings and a bounded above complex `N` of `A`-modules with terms flat over `R`, the comparison
`N ⊗ᴸ_R R' ⟶ N ⊗ᴸ_A A'` of Stacks 065Z followed by `N ⊗ᴸ_A A' ⟶ N ⊗_A A'` is an isomorphism. -/
theorem isIso_ringHomSquareComparison_comp_comparison_of_flat
    (hpo : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g) (CommRingCat.ofHom h)
      (CommRingCat.ofHom i))
    (N : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ) [N.IsStrictlyLE b]
    (hN : ∀ n, Module.Flat R ((ModuleCat.restrictScalars.{u} f).obj (N.X n))) :
    IsIso ((ringHomSquareComparison f g h i sq).app (DerivedCategory.Q.obj N) ≫
      (ModuleCat.restrictScalars.{u} i).mapDerivedCategory.map
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          h).comparison.app N)) := by
  let Nf : CochainComplex (ModuleCat.{u} R) ℤ :=
    ((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj N
  have : Nf.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun n hn => (ModuleCat.restrictScalars.{u} f).map_isZero
      (N.isZero_of_isStrictlyLE b n hn)
  have : ∀ n, Module.Flat R (Nf.X n) := hN
  have hcomp := derivedBaseChangeComparison_snd_app_comp_counit.{u, u, u, u, u} f g h i sq
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} g).functor
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} h).functor
    (extensionComparison g) (extensionComparison h) N
  have : IsIso ((extensionComparison g).app Nf) := isIso_extensionComparison_app g Nf
    (CochainComplex.KFlat.kFlat_of_flat.{u, u} Nf b)
  have : IsIso ((NatTrans.mapHomologicalComplex (underivedSquareComparison f g h i sq)
      (ComplexShape.up ℤ)).app N) := by
    have : ∀ n, IsIso (((NatTrans.mapHomologicalComplex (underivedSquareComparison f g h i sq)
        (ComplexShape.up ℤ)).app N).f n) := fun n =>
      isIso_underivedSquareComparison_app_of_isPushout f g h i sq hpo (N.X n)
    exact HomologicalComplex.Hom.isIso_of_components _
  have hR : IsIso ((ringHomSquareComparison f g h i sq).app (DerivedCategory.Q.obj N) ≫
      (ModuleCat.restrictScalars.{u} i).mapDerivedCategory.map ((extensionComparison h).app N) ≫
      (ModuleCat.restrictScalars.{u} i).mapDerivedCategoryFactors.hom.app
        (((ModuleCat.extendScalars.{u, u, u} h).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          N)) :=
    (congrArg IsIso hcomp).mpr inferInstance
  rw [← Category.assoc] at hR
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _
    ((ModuleCat.restrictScalars.{u} i).mapDerivedCategoryFactors.hom.app
      (((ModuleCat.extendScalars.{u, u, u} h).mapHomologicalComplex (ComplexShape.up ℤ)).obj N))
    (Iso.isIso_hom ((ModuleCat.restrictScalars.{u} i).mapDerivedCategoryFactors.app _)) hR

end RingTheory.TorIndependence

module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportTowerExcision
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedLinear
public import StacksFrontier.Algebra.Homology.DerivedHomologyLinear
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.ShriekConstantCohomology
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicCompactSupportFunctoriality

/-!
# `Hⁱ_c(X_k̄, -)` is `Λ`-linear

Let `Λ` be a commutative ring, `k` a finite field, `f : X ⟶ Spec k` with a compactification `j`
and `k̄` an extension of `k`. The functor `G ↦ Hⁱ_c(X_k̄, G)`
(`Stacks.EtaleCohomology.compactSupportSheafCohomology`) from sheaves of `Λ`-modules on `X_étale`
to `Λ`-modules is `Λ`-linear: multiplication by `a ∈ Λ` on `G` induces multiplication by `a` on
`Hⁱ_c(X_k̄, G)`. Every step of `RΓ_c(X_k̄, -)` is: extension by zero and inverse image are left
adjoints of functors computed sectionwise, the localization functors `K⁺ ⥤ D⁺` and the homology
functors are linear, and a total right derived functor of a linear functor is linear
(`CategoryTheory.Functor.linear_of_isRightDerivedFunctor`).

## Main results

* `Stacks.EtaleCohomology.rightDerivedFunctorPlus_linear_of_functorLinear`.
* `Stacks.EtaleCohomology.compactSupportFrobeniusFunctor_linear`.
* `Stacks.EtaleCohomology.compactSupportSheafCohomology_additive`,
  `Stacks.EtaleCohomology.compactSupportSheafCohomology_linear`.

## Implementation notes

`Stacks.EtaleCohomology.compactSupportSheafCohomology` lives in the standard model
`HasDerivedCategory.standard`, which is therefore a local instance in the étale section; the
general statements are model-free.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

section Plus

variable (R : Type*) [CommRing R] {C D : Type*} [Category C] [Category D] [Abelian C]
  [Abelian D] [Linear R C] [Linear R D] [HasDerivedCategory C] [HasDerivedCategory D]

/-- A functor into a category `B` is `R`-linear if its composite with a faithful linear
functor `ι : B ⥤ E` sends `a • 𝟙 Z` to `a • 𝟙 _`. -/
private theorem functorLinear_of_map_smul_id {A B E : Type*} [Category A] [Category B]
    [Category E] [Preadditive A] [Preadditive B] [Preadditive E] [Linear R A] [Linear R B]
    [Linear R E] (F : A ⥤ B) (ι : B ⥤ E) [ι.Faithful] [ι.Additive] [ι.Linear R]
    (h : ∀ (Z : A) (a : R), ι.map (F.map (a • 𝟙 Z)) = a • 𝟙 (ι.obj (F.obj Z))) :
    Functor.Linear R F := by
  rw [Functor.linear_iff]
  intro Z a
  apply ι.map_injective
  rw [h, ι.map_smul, ι.map_id]

/-- **The localization `K⁺(C) ⥤ D⁺(C)` is `R`-linear**: the unbounded `K(C) ⥤ D(C)` is, and
`D⁺(C) ⥤ D(C)` is a faithful inclusion. -/
theorem plusQh_functorLinear : Functor.Linear R (DerivedCategory.Plus.Qh (C := C)) :=
  functorLinear_of_map_smul_id R _ DerivedCategory.Plus.ι fun _ a =>
    (Functor.linear_iff (R := R) DerivedCategory.Qh).mp inferInstance _ a

/-- **The localization `C⁺(C) ⥤ D⁺(C)` is `R`-linear.** -/
theorem plusQ_functorLinear : Functor.Linear R (DerivedCategory.Plus.Q (C := C)) :=
  functorLinear_of_map_smul_id R _ DerivedCategory.Plus.ι fun _ a =>
    (Functor.linear_iff (R := R) DerivedCategory.Q).mp inferInstance _ a

omit [HasDerivedCategory C] [HasDerivedCategory D] in
/-- **A linear functor is linear on bounded below complexes.** -/
theorem mapCochainComplexPlus_functorLinear (F : C ⥤ D) [F.Additive] [F.Linear R] :
    Functor.Linear R F.mapCochainComplexPlus :=
  functorLinear_of_map_smul_id R _ (CochainComplex.Plus.ι D) fun _ a =>
    (Functor.linear_iff (R := R) (F.mapHomologicalComplex _)).mp inferInstance _ a

/-- **The derived functor `RF : D⁺(C) ⥤ D⁺(D)` of an `R`-linear functor is `R`-linear**: it is a
right derived functor of `K⁺(F)` followed by the linear localization, along the linear
localization `K⁺(C) ⥤ D⁺(C)`. -/
theorem rightDerivedFunctorPlus_linear_of_functorLinear (F : C ⥤ D) [F.Additive] [F.Linear R]
    [EnoughInjectives C] : Functor.Linear R F.rightDerivedFunctorPlus := by
  have := plusQh_functorLinear R (C := C)
  have := plusQh_functorLinear R (C := D)
  have : Functor.Linear R F.mapHomotopyCategoryPlus :=
    functorLinear_of_map_smul_id R _ (HomotopyCategory.Plus.ι D) fun _ a =>
      (Functor.linear_iff (R := R) (F.mapHomotopyCategory (.up ℤ))).mp inferInstance _ a
  exact Functor.linear_of_isRightDerivedFunctor R (HomotopyCategory.Plus.quasiIso C)
    F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnit

/-- **The homology functors of `D⁺(C)` are `R`-linear.** -/
theorem plusHomologyFunctor_functorLinear (i : ℤ) :
    Functor.Linear R (DerivedCategory.Plus.homologyFunctor C i) :=
  inferInstanceAs (Functor.Linear R (DerivedCategory.Plus.ι ⋙ DerivedCategory.homologyFunctor C i))

end Plus

section Etale

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [CommRing Λ]

/-- **Inverse image of sheaves of `Λ`-modules is `Λ`-linear**, being left adjoint to the direct
image, which is computed sectionwise. -/
theorem etaleModuleInverseImage_functorLinear {X Y : Scheme.{u}} (g : X ⟶ Y) :
    Functor.Linear Λ (etaleModuleInverseImage.{u, 0} Λ g) := by
  rw [Functor.linear_iff]
  exact fun G a => map_smul_id_of_adjunction Λ
    (etaleModuleInverseImageAdj.{u, 0} Λ g) (fun _ _ => rfl) G a

/-- **Extension by zero of sheaves of `Λ`-modules is `Λ`-linear.** -/
theorem etaleModuleExtensionByZero_functorLinear {U X : Scheme.{u}} (g : U ⟶ X) [Etale g] :
    Functor.Linear Λ (etaleModuleExtensionByZero.{u, 0} Λ g) := by
  rw [Functor.linear_iff]
  exact etaleModuleExtensionByZero_map_smul_id Λ g

/-- **A sheaf placed in degree `0` depends `Λ`-linearly on the sheaf.** -/
theorem sheafSingleComplex_functorLinear {X : Scheme.{u}} :
    Functor.Linear Λ (sheafSingleComplex Λ (X := X)) := by
  refine functorLinear_of_map_smul_id Λ _ (CochainComplex.Plus.ι (EtaleModules.{u, 0} Λ X))
    fun G a => ?_
  change (HomologicalComplex.single (EtaleModules.{u, 0} Λ X) (ComplexShape.up ℤ) 0).map
      (a • 𝟙 G) = a • 𝟙 _
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  obtain rfl | h := eq_or_ne i 0
  · simp only [HomologicalComplex.single_map_f_self, Linear.smul_comp, Category.id_comp,
      Linear.comp_smul, Iso.hom_inv_id, HomologicalComplex.smul_f_apply, HomologicalComplex.id_f]
    rfl
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ h).eq_of_src _ _

variable {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]

omit [Fintype k] in
/-- **`RΓ_c(X_k̄, -)` is `Λ`-linear.** -/
theorem compactSupportFrobeniusFunctor_linear :
    Functor.Linear Λ (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar) := by
  have := etaleModuleExtensionByZero_functorLinear Λ j.immersion
  have := etaleModuleInverseImage_functorLinear Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)
  have := mapCochainComplexPlus_functorLinear Λ (etaleModuleExtensionByZero.{u, 0} Λ j.immersion)
  have := mapCochainComplexPlus_functorLinear Λ
    (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar))
  have := plusQ_functorLinear Λ
    (C := EtaleModules.{u, 0} Λ (fieldBaseChange (Over.mk j.toBase) kbar))
  have : Functor.Linear Λ (etaleModuleDirectImage.{u, 0} Λ
      (pullback.snd (Over.mk j.toBase).hom (Stacks.Frobenius.specAlgebraMap k kbar))) :=
    ⟨fun _ _ => rfl⟩
  have := rightDerivedFunctorPlus_linear_of_functorLinear Λ (etaleModuleDirectImage.{u, 0} Λ
    (pullback.snd (Over.mk j.toBase).hom (Stacks.Frobenius.specAlgebraMap k kbar)))
  have := rightDerivedFunctorPlus_linear_of_functorLinear Λ
    (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
  unfold compactSupportFrobeniusFunctor fieldBaseChangeRestrictionFunctor
  infer_instance

omit [Fintype k] in
/-- **`Hⁱ_c(X_k̄, -)` is additive.** -/
theorem compactSupportSheafCohomology_additive (i : ℤ) :
    (compactSupportSheafCohomology Λ f j kbar i).Additive := by
  have := additive_liftSingle Λ X (fun _ => ⟨0, inferInstance⟩)
  dsimp only [compactSupportSheafCohomology, sheafSingleComplex]
  infer_instance

omit [Fintype k] in
/-- **`Hⁱ_c(X_k̄, -)` is `Λ`-linear**: multiplication by `a ∈ Λ` on a sheaf `G` induces
multiplication by `a` on `Hⁱ_c(X_k̄, G)`. -/
theorem compactSupportSheafCohomology_linear (i : ℤ) :
    Functor.Linear Λ (compactSupportSheafCohomology Λ f j kbar i) := by
  have := sheafSingleComplex_functorLinear Λ (X := X)
  have := compactSupportFrobeniusFunctor_linear Λ f j kbar
  have := plusHomologyFunctor_functorLinear Λ (C := ModuleCat.{u + 1} Λ) i
  unfold compactSupportSheafCohomology
  infer_instance

end Etale

end Stacks.EtaleCohomology

end

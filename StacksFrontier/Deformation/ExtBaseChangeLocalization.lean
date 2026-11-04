module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.Deformation.ExtBaseChangeVanishing

/-!
# Power torsion of an Ext class from the vanishing of a localized base change

Let `R` be a Noetherian ring, let `g ∈ R` and let `S` be the localization of `R` at `g`. For a
finite `R`-module `M`, an arbitrary `R`-module `N` and a class in `Ext^i_R(M, N)` whose derived
base change to `S` vanishes, the class is killed by a power of `g`: base change of `Ext` along
the flat map `R → S` is computed by the Ext--tensor comparison of Stacks 087Q, and an element of
a module which dies in the localization at `g` is killed by a power of `g`.

This is the converse direction of `Deformation.ExtBaseChange.eq_zero_of_map_eq_zero_of_singleIso`
and is the input of Stacks 05EC that the source's proof of Stacks 0DZ2 uses to turn local
liftability of the module into the power-torsion hypothesis on the obstruction class.

## Main results

* `Deformation.exists_pow_smul_eq_zero_of_mem_map`: power torsion at the elements of an ideal
  spreads to the ideal they generate after a ring map.
* `Deformation.ExtBaseChange.exists_pow_smul_eq_zero_of_map_hom_eq_zero`: an `Ext` class whose
  derived base change to a localization at `g` vanishes is killed by a power of `g`.
* `Deformation.ExtBaseChange.exists_pow_smul_eq_zero_of_map_eq_zero_of_singleIso`: the same read
  on a morphism of the derived category between single complexes.

## References

* [Stacks Project, Tag 05EC](https://stacks.math.columbia.edu/tag/05EC)
* [Stacks Project, Tag 087Q](https://stacks.math.columbia.edu/tag/087Q)
* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct

universe u

namespace Deformation

/-- If an element of an `S`-module is killed by a power of the image of every element of an
ideal `I` of `R`, then it is killed by a power of every element of the ideal `I` generates in
`S`: the annihilator radical is an ideal, so it contains that extension. -/
theorem exists_pow_smul_eq_zero_of_mem_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R) {M : Type*} [AddCommGroup M] [Module S M] {m : M}
    (h : ∀ g ∈ I, ∃ n : ℕ, (φ g) ^ n • m = 0) :
    ∀ a ∈ I.map φ, ∃ n : ℕ, a ^ n • m = 0 := by
  have hsub : I.map φ ≤ ((S ∙ m).annihilator).radical := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    obtain ⟨n, hn⟩ := h g hg
    exact ⟨n, (Submodule.mem_annihilator_span_singleton _ _).mpr hn⟩
  intro a ha
  obtain ⟨n, hn⟩ := hsub ha
  exact ⟨n, (Submodule.mem_annihilator_span_singleton _ _).mp hn⟩

namespace ExtBaseChange

attribute [local instance] HasDerivedCategory.standard

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- **The localization step of Stacks 05EC for an `Ext` class.** Let `R` be Noetherian, `M` a
finite `R`-module, `N` any `R`-module and `S` a localization of `R` at `g`. A class in
`Ext^i_R(M, N)` whose derived base change to `S` vanishes is killed by a power of `g`. -/
public theorem exists_pow_smul_eq_zero_of_map_hom_eq_zero
    [IsNoetherianRing R] (g : R) [IsLocalization.Away g S]
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]
    [F.CommShift ℤ]
    {M N : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] {i : ℕ}
    (x : Ext.{u} (ModuleCat.of R (ULift.{u} M)) (ModuleCat.of R (ULift.{u} N)) i)
    (hx : F.map x.hom = 0) :
    ∃ n : ℕ, g ^ n • x = 0 := by
  have hflat : Module.Flat R S := IsLocalization.flat S (Submonoid.powers g)
  have h1 : (1 : S) ⊗ₜ[R] x =
      (0 : TensorProduct R S
        (Ext.{u} (ModuleCat.of R (ULift.{u} M)) (ModuleCat.of R (ULift.{u} N)) i)) :=
    one_tmul_eq_zero_of_comp_mk₀_unit_eq_zero hflat x
      (StacksDraft.DerivedHom.SingleBaseChange.ext_comp_mk₀_unit_eq_zero hflat F comparison x hx)
  have hloc : IsLocalizedModule (Submonoid.powers g)
      (TensorProduct.mk R S
        (Ext.{u} (ModuleCat.of R (ULift.{u} M)) (ModuleCat.of R (ULift.{u} N)) i) 1) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers g) S _).mpr
      (TensorProduct.isBaseChange R _ S)
  exact Deformation.exists_pow_smul_eq_zero_of_localization_eq_zero g
    (TensorProduct.mk R S _ 1) h1

/-- **The localization step of Stacks 05EC for a morphism of `D(R)`.** In the situation of
`exists_pow_smul_eq_zero_of_map_hom_eq_zero`, a morphism `ω : K ⟶ T⟦i⟧` whose source and target
are isomorphic to the single complexes on a finite module `M` and on an arbitrary module `N` is
killed by a power of `g` as soon as its derived base change to the localization vanishes. -/
public theorem exists_pow_smul_eq_zero_of_map_eq_zero_of_singleIso
    [IsNoetherianRing R] (g : R) [IsLocalization.Away g S]
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]
    [F.CommShift ℤ]
    {M N : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N]
    {K T : DerivedCategory (ModuleCat.{u} R)} {i : ℕ}
    (eK : K ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      (ModuleCat.of R (ULift.{u} M)))
    (eT : T ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      (ModuleCat.of R (ULift.{u} N)))
    (ω : K ⟶ T⟦(i : ℤ)⟧) (hω : F.map ω = 0) :
    ∃ n : ℕ, g ^ n • ω = 0 := by
  let e : Ext.{u} (ModuleCat.of R (ULift.{u} M)) (ModuleCat.of R (ULift.{u} N)) i ≃ₗ[R]
      (K ⟶ T⟦(i : ℤ)⟧) :=
    (Ext.homLinearEquiv (R := R)).trans (Linear.homCongr R eK.symm
      ((shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (i : ℤ)).mapIso eT).symm)
  have hcoe : ∀ y : Ext.{u} (ModuleCat.of R (ULift.{u} M))
      (ModuleCat.of R (ULift.{u} N)) i, e y =
      eK.hom ≫ y.hom ≫ (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (i : ℤ)).map eT.inv :=
    fun y => by simp [e, Linear.homCongr_apply]
  set x := e.symm ω with hxdef
  have hxe : e x = ω := e.apply_symm_apply ω
  have hxh : x.hom =
      eK.inv ≫ ω ≫ (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (i : ℤ)).map eT.hom := by
    have h := (hcoe x).symm.trans hxe
    rw [← h]
    simp [← Functor.map_comp]
  have hFx : F.map x.hom = 0 := by rw [hxh]; simp [hω]
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_map_hom_eq_zero g F comparison x hFx
  refine ⟨n, ?_⟩
  rw [← hxe, ← map_smul, hn, map_zero]

end ExtBaseChange

end Deformation

end

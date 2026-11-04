module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import StacksFrontier.Deformation.FlatModuleLiftEquivalence
public import StacksFrontier.Homology.HomComplex.RHom.SingleBaseChangeUnit
public import StacksFrontier.Homology.PseudoCoherent.HomFlat

/-!
# Vanishing of an Ext class from the vanishing of its flat base change

Let `R` be a Noetherian ring, `S` a flat `R`-algebra inducing an isomorphism `R/I ≅ S/IS` for a
finitely generated ideal `I`, let `M` be a finite `R`-module and `N` any `R`-module. For a class
`x` in `Ext^i_R(M, N)` which is killed by a power of every element of `I`, the vanishing of the
derived base change of `x` to `S` forces `x` itself to vanish.

Two inputs do the work. Base change of Ext along a flat algebra is computed by the Ext--tensor
comparison of Stacks 087Q, which for a finite module over a Noetherian ring is bijective in
every degree; this turns the vanishing of `x` composed with the unit `N ⟶ S ⊗_R N` into the
vanishing of `1 ⊗ x`. The injectivity of base change on the `I`-primary component, Stacks 05EC,
then gives `x = 0`.

## Main definitions

* `Deformation.ExtBaseChange.restrictSelfEquiv`: `S` as an `R`-module through `algebraMap`,
  identified with the restriction of scalars of `S` as a module over itself.
* `Deformation.ExtBaseChange.tensorUnitIso`: the `R`-linear identification of `N ⊗_R S` with the
  restriction of scalars of `S ⊗_R N`.

## Main results

* `Deformation.ExtBaseChange.one_tmul_eq_zero_of_comp_mk₀_unit_eq_zero`: a class in
  `Ext^i_R(M, N)` killed by composition with the unit `N ⟶ S ⊗_R N` has `1 ⊗ x = 0` in
  `S ⊗_R Ext^i_R(M, N)`, for `M` finite over a Noetherian ring and `S` flat.
* `Deformation.ExtBaseChange.ext_eq_zero_of_map_hom_eq_zero`: an `I`-power-torsion class in
  `Ext^i_R(M, N)` whose derived base change to `S` vanishes is zero. This is the comparison step
  of Stacks 0DZ2 for the obstruction class, in the form the source's proof uses it.

## References

* [Stacks Project, Tag 05EC](https://stacks.math.columbia.edu/tag/05EC)
* [Stacks Project, Tag 087Q](https://stacks.math.columbia.edu/tag/087Q)
* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct

universe u

namespace Deformation.ExtBaseChange

attribute [local instance] HasDerivedCategory.standard

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- `S` as an `R`-module through `algebraMap`, identified with the restriction of scalars along
`algebraMap R S` of `S` as a module over itself. The two differ only in the recorded
`R`-action. -/
public def restrictSelfEquiv :
    ((ModuleCat.restrictScalars.{u, u, u} (algebraMap R S)).obj (ModuleCat.of S S) : Type u)
      ≃ₗ[R] S :=
  { AddEquiv.refl S with
    map_smul' := fun r x => (Algebra.smul_def (R := R) (A := S) r x).symm }

/-- The `R`-linear identification of `N ⊗_R S` with the restriction of scalars of the extension
of scalars `S ⊗_R N`: it exchanges the two tensor factors. -/
public def tensorUnitIso (N : ModuleCat.{u} R) :
    ModuleCat.of R (TensorProduct R (N : Type u) (ULift.{u} S)) ≅
      (ModuleCat.restrictScalars.{u, u, u} (algebraMap R S)).obj
        ((ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).obj N) :=
  LinearEquiv.toModuleIso
    ((TensorProduct.congr (LinearEquiv.refl R (N : Type u))
          (ULift.moduleEquiv.trans (restrictSelfEquiv (R := R) (S := S)).symm)).trans
      (TensorProduct.comm R _ _))

/-- Read on `n ⊗ 1`, the identification `tensorUnitIso` is the unit `n ↦ 1 ⊗ n` of the
change-of-rings adjunction. -/
public theorem tensorElementHom_comp_tensorUnitIso_hom (N : ModuleCat.{u} R) :
    StacksDraft.PseudoCoherence.tensorElementHom R N
          (ModuleCat.of R (ULift.{u} S)) (ULift.up (1 : S)) ≫
        (tensorUnitIso (R := R) (S := S) N).hom =
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap R S)).unit.app N := by
  ext n
  rfl

/-- **The unit detects the flat base change of an Ext class.** Let `R` be Noetherian, `M` a
finite `R`-module, `N` any `R`-module and `S` a flat `R`-algebra. A class in `Ext^i_R(M, N)`
killed by composition with the degree-zero class of the unit `N ⟶ S ⊗_R N` has vanishing base
change `1 ⊗ x` in `S ⊗_R Ext^i_R(M, N)`. -/
public theorem one_tmul_eq_zero_of_comp_mk₀_unit_eq_zero
    [IsNoetherianRing R] (hflat : Module.Flat R S)
    {M N : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] {i : ℕ}
    (x : Ext.{u} (ModuleCat.of R (ULift.{u} M)) (ModuleCat.of R (ULift.{u} N)) i)
    (hx : x.comp (Ext.mk₀ ((ModuleCat.extendRestrictScalarsAdj.{u, u, u}
        (algebraMap R S)).unit.app (ModuleCat.of R (ULift.{u} N)))) (add_zero i) = 0) :
    (1 : S) ⊗ₜ[R] x =
      (0 : TensorProduct R S
        (Ext.{u} (ModuleCat.of R (ULift.{u} M)) (ModuleCat.of R (ULift.{u} N)) i)) := by
  have := hflat
  have h1 : x.comp (Ext.mk₀ (StacksDraft.PseudoCoherence.tensorElementHom R
      (ModuleCat.of R (ULift.{u} N)) (ModuleCat.of R (ULift.{u} S)) (ULift.up (1 : S))))
      (add_zero i) = 0 := by
    have h2 := tensorElementHom_comp_tensorUnitIso_hom (R := R) (S := S)
      (ModuleCat.of R (ULift.{u} N))
    rw [← Category.comp_id (StacksDraft.PseudoCoherence.tensorElementHom R
      (ModuleCat.of R (ULift.{u} N)) (ModuleCat.of R (ULift.{u} S)) (ULift.up (1 : S))),
      ← Iso.hom_inv_id (tensorUnitIso (R := R) (S := S) (ModuleCat.of R (ULift.{u} N))),
      ← Category.assoc, ← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero, h2, hx,
      Ext.zero_comp]
  have hbij := StacksDraft.PseudoCoherence.canonicalExtTensorComparison_bijective_of_noetherian
    R M N S i
  have h4 : StacksDraft.PseudoCoherence.canonicalExtTensorComparison R
      (ModuleCat.of R (ULift.{u} M)) (ModuleCat.of R (ULift.{u} N))
      (ModuleCat.of R (ULift.{u} S)) i (x ⊗ₜ[R] ULift.up (1 : S)) = 0 := by
    rw [StacksDraft.PseudoCoherence.canonicalExtTensorComparison_tmul]
    exact h1
  have h5 : x ⊗ₜ[R] (ULift.up (1 : S) :
      (ModuleCat.of R (ULift.{u} S) : Type u)) = 0 := by
    refine hbij.injective ?_
    rw [h4, map_zero]
  have hflip : (1 : S) ⊗ₜ[R] x =
      ((TensorProduct.comm R
          (Ext.{u} (ModuleCat.of R (ULift.{u} M)) (ModuleCat.of R (ULift.{u} N)) i)
          (ULift.{u} S)).trans
        (TensorProduct.congr (ULift.moduleEquiv (R := R) (M := S)) (LinearEquiv.refl R _)))
        (x ⊗ₜ[R] ULift.up (1 : S)) := by
    simp
  rw [hflip, h5, map_zero]

/-- **The comparison step of Stacks 0DZ2 for an Ext class.** Let `R` be Noetherian, `S` a flat
`R`-algebra inducing an isomorphism `R/I ≅ S/IS` for a finitely generated ideal `I`, let `M` be a
finite `R`-module and `N` any `R`-module, and let `F` be a total left derived functor of termwise
extension of scalars. A class in `Ext^i_R(M, N)` killed by a power of every element of `I` whose
derived base change under `F` vanishes is itself zero. -/
public theorem ext_eq_zero_of_map_hom_eq_zero
    [IsNoetherianRing R] (hflat : Module.Flat R S)
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]
    [F.CommShift ℤ]
    (I : Ideal R) (hI : I.FG)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    {M N : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] {i : ℕ}
    (x : Ext.{u} (ModuleCat.of R (ULift.{u} M)) (ModuleCat.of R (ULift.{u} N)) i)
    (hx : F.map x.hom = 0)
    (hloc : ∀ g ∈ I, ∃ k : ℕ, g ^ k • x = 0) :
    x = 0 :=
  Deformation.eq_zero_of_one_tmul_eq_zero.{u, u} I hI hflat hq
    (Deformation.mem_primaryComponent_of_forall_exists_pow_smul_eq_zero hI hloc)
    (one_tmul_eq_zero_of_comp_mk₀_unit_eq_zero hflat x
      (StacksDraft.DerivedHom.SingleBaseChange.ext_comp_mk₀_unit_eq_zero
        hflat F comparison x hx))

/-- **The comparison step of Stacks 0DZ2 for a morphism of `D(R)`.** In the situation of
`ext_eq_zero_of_map_hom_eq_zero`, a morphism `ω : K ⟶ T⟦i⟧` whose source and target are
isomorphic to the single complexes on a finite module `M` and on an arbitrary module `N`
vanishes as soon as it is killed by a power of every element of `I` and its derived base change
under `F` vanishes.

The hypothesis and the conclusion are read on the morphism, not on the corresponding `Ext`
class: the `R`-linear identification of `Hom_{D(R)}(K, T⟦i⟧)` with `Ext^i_R(M, N)` transports
both, because `Abelian.Ext.homLinearEquiv` is `R`-linear and composition with an isomorphism
is `R`-linear. -/
public theorem eq_zero_of_map_eq_zero_of_singleIso
    [IsNoetherianRing R] (hflat : Module.Flat R S)
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]
    [F.CommShift ℤ]
    (I : Ideal R) (hI : I.FG)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    {M N : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N]
    {K T : DerivedCategory (ModuleCat.{u} R)} {i : ℕ}
    (eK : K ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      (ModuleCat.of R (ULift.{u} M)))
    (eT : T ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      (ModuleCat.of R (ULift.{u} N)))
    (ω : K ⟶ T⟦(i : ℤ)⟧) (hω : F.map ω = 0)
    (hloc : ∀ g ∈ I, ∃ k : ℕ, g ^ k • ω = 0) :
    ω = 0 := by
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
  have hlocx : ∀ g ∈ I, ∃ k : ℕ, g ^ k • x = 0 := by
    intro g hg
    obtain ⟨k, hk⟩ := hloc g hg
    refine ⟨k, e.injective ?_⟩
    rw [map_smul, hxe, hk, map_zero]
  have hxh : x.hom =
      eK.inv ≫ ω ≫ (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (i : ℤ)).map eT.hom := by
    have h := (hcoe x).symm.trans hxe
    rw [← h]
    simp [← Functor.map_comp]
  have hFx : F.map x.hom = 0 := by rw [hxh]; simp [hω]
  have hx0 : x = 0 :=
    ext_eq_zero_of_map_hom_eq_zero hflat F comparison I hI hq x hFx hlocx
  rw [← hxe, hx0, map_zero]

end Deformation.ExtBaseChange

end

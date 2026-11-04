module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.CategoryTheory.Abelian.SerreClass.Bousfield
public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
public import StacksCore.Algebra.Category.ModuleCat.Localization
public import StacksCore.Tactic.StacksAttribute

/-!
# Localization of modules as a Serre quotient

Let `S` be a submonoid of a commutative ring `R`. The `R`-modules in which every element is
annihilated by some member of `S` form a Serre subcategory of `ModuleCat R`, and the localization
functor presents the category of modules over `Localization S` as the quotient by this Serre
subcategory.

The localization functor is a left adjoint to restriction of scalars along `R → Localization S`,
and that restriction is fully faithful, so the general criterion for a left adjoint with fully
faithful right adjoint identifies the localization as the Serre quotient by the kernel of the
localization functor. That kernel is computed to be exactly the `S`-torsion modules.

## Main definitions

* `Stacks.Examples.localizationTorsionModuleProperty`: the class of modules whose elements are
  individually annihilated by elements of `S`.

## Main results

* `Stacks.Examples.localizationTorsionModuleProperty_isSerreClass`: these modules form a Serre
  subcategory.
* `Stacks.Examples.localizedModuleFunctor_isLocalization`: localization of modules is the
  categorical localization at the morphisms whose kernel and cokernel are `S`-torsion.

## Implementation notes

The Serre quotient is represented by the localization at
`localizationTorsionModuleProperty S |>.isoModSerre`. Stating that the usual module localization
functor is a localization at this morphism class includes the canonical equivalence with its
constructed localization category, together with compatibility with the quotient functor, via
`CategoryTheory.Localization.equivalenceFromModel` and
`CategoryTheory.Localization.qCompEquivalenceFromModelFunctorIso`.

## References

* [Stacks Project, Tag 0EA5](https://stacks.math.columbia.edu/tag/0EA5)
-/

@[expose] public noncomputable section

universe u v

namespace Stacks.Examples

open CategoryTheory CategoryTheory.Limits

/-- An `R`-module is `S`-torsion if each of its elements is annihilated by some element of
`S`. -/
public def localizationTorsionModuleProperty {R : Type u} [CommRing R]
    (S : Submonoid R) : ObjectProperty (ModuleCat.{v} R) :=
  fun M ↦ ∀ x : M, ∃ s : S, (s : R) • x = 0

/-- The modules whose elements are annihilated locally by `S` form a Serre subcategory. -/
@[stacks 0EA5 "the Serre subcategory"]
public instance localizationTorsionModuleProperty_isSerreClass {R : Type u} [CommRing R]
    (S : Submonoid R) :
    (localizationTorsionModuleProperty (R := R) S :
      ObjectProperty (ModuleCat.{v} R)).IsSerreClass := by
  refine {
    exists_zero := ?_
    prop_of_mono := ?_
    prop_of_epi := ?_
    prop_X₂_of_shortExact := ?_ }
  · exact ⟨ModuleCat.of R PUnit, ModuleCat.isZero_of_subsingleton _, fun x =>
      ⟨1, by rw [Subsingleton.elim x 0, smul_zero]⟩⟩
  · intro X Y f hf hY x
    obtain ⟨s, hs⟩ := hY (f.hom x)
    refine ⟨s, ?_⟩
    apply (ModuleCat.mono_iff_injective f).mp inferInstance
    simp only [map_smul, hs, map_zero]
  · intro X Y f hf hX y
    obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective f).mp inferInstance y
    obtain ⟨s, hs⟩ := hX x
    exact ⟨s, by simpa only [map_smul, map_zero] using congr_arg f.hom hs⟩
  · intro T hT h₁ h₃ x
    obtain ⟨s, hs⟩ := h₃ (T.g.hom x)
    have hrange : (s : R) • x ∈ LinearMap.range T.f.hom := by
      rw [ShortComplex.Exact.moduleCat_range_eq_ker hT.exact]
      exact LinearMap.mem_ker.mpr (by simp only [map_smul, hs])
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hrange
    obtain ⟨t, ht⟩ := h₁ y
    refine ⟨t * s, ?_⟩
    have ht' : (t : R) • ((s : R) • x) = 0 := by
      rw [← hy, ← map_smul, ht, map_zero]
    simpa only [Submonoid.coe_mul, smul_smul] using ht'

/-- The `R`-module structure on a localized module, used to restrict scalars along
`R → Localization S`. -/
private instance localizedModuleFunctor_obj_module {R : Type u} [CommRing R]
    (S : Submonoid R) [Small.{v, u} R] (M : ModuleCat.{v} R) :
    Module R ((ModuleCat.localizedModuleFunctor.{v} S).obj M : Type v) :=
  ModuleCat.instModuleCarrierLocalizationLocalizedModule M S

private instance localizedModuleFunctor_obj_isScalarTower {R : Type u} [CommRing R]
    (S : Submonoid R) [Small.{v, u} R] (M : ModuleCat.{v} R) :
    IsScalarTower R (Localization S) ((ModuleCat.localizedModuleFunctor.{v} S).obj M : Type v) :=
  by change IsScalarTower R (Localization S) (M.localizedModule S); infer_instance

/-- The `R`-module structure on a module over `Localization S` by restriction of scalars. -/
private instance moduleCat_localization_module {R : Type u} [CommRing R] (S : Submonoid R)
    (N : ModuleCat.{v} (Localization S)) : Module R N :=
  Module.compHom N (algebraMap R (Localization S))

private instance moduleCat_localization_isScalarTower {R : Type u} [CommRing R] (S : Submonoid R)
    (N : ModuleCat.{v} (Localization S)) : IsScalarTower R (Localization S) N :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

private instance localizedModuleFunctor_obj_compatibleSMul {R : Type u} [CommRing R]
    (S : Submonoid R) [Small.{v, u} R] (M : ModuleCat.{v} R) (N : ModuleCat.{v} (Localization S)) :
    LinearMap.CompatibleSMul ((ModuleCat.localizedModuleFunctor.{v} S).obj M : Type v) N R
      (Localization S) :=
  ⟨fun g r x => g.map_smul_of_tower r x⟩

/-- The extension of a map `M ⟶ N` of `R`-modules to the localization of `M`. -/
private noncomputable def localizedModuleLift {R : Type u} [CommRing R]
    (S : Submonoid R) [Small.{v, u} R] (M : ModuleCat.{v} R)
    (N : ModuleCat.{v} (Localization S))
    (f : M ⟶ (ModuleCat.restrictScalars.{v} (algebraMap R (Localization S))).obj N) :
    (ModuleCat.localizedModuleFunctor.{v} S).obj M ⟶ N :=
  ModuleCat.ofHom <|
    (IsLocalizedModule.lift S (M.localizedModuleMkLinearMap S) f.hom
      (fun s => ModuleCat.invertibleSMul_of_isScalarTower S (Localization S)
        ((ModuleCat.restrictScalars.{v} (algebraMap R (Localization S))).obj N)
        s)).extendScalarsOfIsLocalization S (Localization S)

private theorem localizedModuleLift_apply_mk {R : Type u} [CommRing R]
    (S : Submonoid R) [Small.{v, u} R] (M : ModuleCat.{v} R)
    (N : ModuleCat.{v} (Localization S))
    (f : M ⟶ (ModuleCat.restrictScalars.{v} (algebraMap R (Localization S))).obj N) (x : M) :
    (localizedModuleLift S M N f).hom (M.localizedModuleMkLinearMap S x) = f.hom x := by
  simp only [localizedModuleLift]
  exact DFunLike.congr_fun (IsLocalizedModule.lift_comp S (M.localizedModuleMkLinearMap S) f.hom
    (fun s => ModuleCat.invertibleSMul_of_isScalarTower S (Localization S)
      ((ModuleCat.restrictScalars.{v} (algebraMap R (Localization S))).obj N) s)) x

private theorem localizedModule_hom_ext {R : Type u} [CommRing R]
    (S : Submonoid R) [Small.{v, u} R] (M : ModuleCat.{v} R)
    (N : ModuleCat.{v} (Localization S)) (f g : (ModuleCat.localizedModuleFunctor.{v} S).obj M ⟶ N)
    (h : ∀ x : M, f.hom (M.localizedModuleMkLinearMap S x) =
      g.hom (M.localizedModuleMkLinearMap S x)) :
    f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.restrictScalars_injective R
  apply IsLocalizedModule.linearMap_ext S (M.localizedModuleMkLinearMap S)
    (LinearMap.id : ((ModuleCat.restrictScalars.{v} (algebraMap R (Localization S))).obj N :
      Type v) →ₗ[R] _)
  ext x
  exact h x

private noncomputable def localizedModuleFunctorHomEquiv {R : Type u} [CommRing R]
    (S : Submonoid R) [Small.{v, u} R] (M : ModuleCat.{v} R)
    (N : ModuleCat.{v} (Localization S)) :
    ((ModuleCat.localizedModuleFunctor.{v} S).obj M ⟶ N) ≃
      (M ⟶ (ModuleCat.restrictScalars.{v} (algebraMap R (Localization S))).obj N) where
  toFun f := ModuleCat.ofHom <| f.hom.restrictScalars R ∘ₗ M.localizedModuleMkLinearMap S
  invFun := localizedModuleLift S M N
  left_inv f := localizedModule_hom_ext S M N _ _ fun x => localizedModuleLift_apply_mk S M N _ x
  right_inv f := by
    apply ModuleCat.hom_ext
    ext x
    exact localizedModuleLift_apply_mk S M N f x

private noncomputable def localizedModuleFunctorCoreHomEquiv {R : Type u} [CommRing R]
    (S : Submonoid R) [Small.{v, u} R] :
    Adjunction.CoreHomEquiv (ModuleCat.localizedModuleFunctor.{v} S)
      (ModuleCat.restrictScalars.{v} (algebraMap R (Localization S))) where
  homEquiv := localizedModuleFunctorHomEquiv S
  homEquiv_naturality_left_symm := by
    intro X' X Y f g
    refine localizedModule_hom_ext S X' Y _ _ fun x => ?_
    change (localizedModuleLift S X' Y (f ≫ g)).hom (X'.localizedModuleMkLinearMap S x) =
      (localizedModuleLift S X Y g).hom ((IsLocalizedModule.mapExtendScalars S
        (X'.localizedModuleMkLinearMap S) (X.localizedModuleMkLinearMap S) (Localization S)
        f.hom) (X'.localizedModuleMkLinearMap S x))
    rw [localizedModuleLift_apply_mk, IsLocalizedModule.mapExtendScalars_apply_apply,
      IsLocalizedModule.map_apply, localizedModuleLift_apply_mk]
    rfl
  homEquiv_naturality_right := by
    intro X Y Y' f g
    apply ModuleCat.hom_ext
    ext x
    rfl

private noncomputable def restrictScalars_fullyFaithful {R : Type u} [CommRing R]
    (S : Submonoid R) [Small.{v, u} R] :
    (ModuleCat.restrictScalars.{v} (algebraMap R (Localization S))).FullyFaithful :=
  Functor.FullyFaithful.comp
    (Equivalence.fullyFaithfulInverse
      (ModuleCat.invertibleSMulEquivalentLocalizationModuleCat.{u, v} S))
    (ObjectProperty.fullyFaithfulι (ModuleCat.invertibleSMul S))

/-- The kernel of the localization functor at `S` is the class of modules whose elements are all
annihilated by members of `S`. -/
public theorem localizedModuleFunctor_kernel_eq {R : Type u} [CommRing R]
    (S : Submonoid R) [Small.{v, u} R] :
    (ModuleCat.localizedModuleFunctor.{v} S).kernel =
      (localizationTorsionModuleProperty (R := R) S : ObjectProperty (ModuleCat.{v} R)) := by
  ext M
  change IsZero ((ModuleCat.localizedModuleFunctor.{v} S).obj M) ↔
    localizationTorsionModuleProperty (R := R) S M
  rw [ModuleCat.isZero_iff_subsingleton]
  change Subsingleton (M.localizedModule S) ↔
    ∀ x : M, ∃ s : S, (s : R) • x = 0
  rw [IsLocalizedModule.subsingleton_iff S (M.localizedModuleMkLinearMap S)]
  exact ⟨fun h x => let ⟨r, hr, hrx⟩ := h x; ⟨⟨r, hr⟩, hrx⟩,
    fun h x => let ⟨s, hs⟩ := h x; ⟨s, s.2, hs⟩⟩

/-- Localizing modules at `S` presents the category of modules over `Localization S` as the Serre
quotient by the modules whose elements are annihilated by members of `S`.

In particular, `CategoryTheory.Localization.equivalenceFromModel` applied to this instance is the
canonical equivalence from the Serre quotient to `ModuleCat (Localization S)`, and
`CategoryTheory.Localization.qCompEquivalenceFromModelFunctorIso` identifies its composite with
the quotient functor with `ModuleCat.localizedModuleFunctor S`. -/
@[stacks 0EA5 "the canonical equivalence",
  stacks 0B0K "the case S = nonzerodivisors: Mod_A modulo torsion is equivalent to Mod_{Q(A)}"]
public instance localizedModuleFunctor_isLocalization {R : Type u} [CommRing R]
    (S : Submonoid R) [Small.{v, u} R] :
    (ModuleCat.localizedModuleFunctor.{v} S).IsLocalization
      (localizationTorsionModuleProperty (R := R) S :
        ObjectProperty (ModuleCat.{v} R)).isoModSerre := by
  let F := ModuleCat.localizedModuleFunctor.{v} S
  let adj := Adjunction.mkOfHomEquiv (localizedModuleFunctorCoreHomEquiv S)
  let : (ModuleCat.restrictScalars.{v} (algebraMap R (Localization S))).Full :=
    (restrictScalars_fullyFaithful S).full
  let : (ModuleCat.restrictScalars.{v} (algebraMap R (Localization S))).Faithful :=
    (restrictScalars_fullyFaithful S).faithful
  have hlocal : F.IsLocalization F.kernel.isoModSerre :=
    Abelian.isLocalization_isoModSerre_kernel_of_leftAdjoint adj
  have hkernel := localizedModuleFunctor_kernel_eq S
  have hW : F.kernel.isoModSerre =
      (localizationTorsionModuleProperty (R := R) S :
        ObjectProperty (ModuleCat.{v} R)).isoModSerre := by
    ext X Y f
    change (F.kernel (kernel f) ∧ F.kernel (cokernel f)) ↔
      (localizationTorsionModuleProperty (R := R) S (kernel f) ∧
        localizationTorsionModuleProperty (R := R) S (cokernel f))
    rw [hkernel]
  exact hW ▸ hlocal

end Stacks.Examples

end

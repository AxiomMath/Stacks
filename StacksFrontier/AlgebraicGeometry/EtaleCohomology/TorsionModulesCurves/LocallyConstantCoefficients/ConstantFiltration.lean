module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.ConstantModuleFiltration
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.RestrictToDenseOpen
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ConstantSheafInverseImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.FiniteCohomologyOfShortExact

/-!
# Finiteness of cohomology along a filtration with constant graded pieces

Let `j' : T ⟶ Y` be an open immersion and `K` a sheaf of `Λ`-modules on `T_étale` killed by an
integer `m`, with a finite filtration whose successive quotients are constant sheaves `M̲` of
finite `Λ`-modules (the conclusion of [Stacks, Tag 0GJ0]). If `H^q(Y, j'_! M̲)` is a finite
`Λ`-module for every finite `Λ`-module `M` killed by `m`, then so is `H^q(Y, j'_! K)`. This is
the dévissage step of the proof of [Stacks, Tag 0GJH]: extension by zero is exact
([Stacks, Tag 03S5]) and Lemma 0GJG passes finiteness through each step of the filtration.

## Main results

* `Stacks.EtaleCohomology.TorsionModules.module_finite_cohomology_extensionByZero_of_relSeries`.

## Implementation notes

The graded pieces given by Tag 0GJ0 are constant sheaves `M̲` of finite modules `M` that need not
themselves be killed by `m`; but `M̲` is, being a subquotient of `K`, and `M̲` is the constant
sheaf of `M / m M`, which is (`constantSheaf_cokernel_nsmul_iso`).

## References

* [Stacks Project, Tag 0GJH](https://stacks.math.columbia.edu/tag/0GJH)
* [Stacks Project, Tag 0GJ0](https://stacks.math.columbia.edu/tag/0GJ0)
* [Stacks Project, Tag 0GJG](https://stacks.math.columbia.edu/tag/0GJG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology.TorsionModules

variable (Λ : Type r) [CommRing Λ]

/-- An object killed by `m` has every subobject killed by `m`. -/
theorem nsmul_id_eq_zero_of_mono {C : Type*} [Category C] [Preadditive C] {A B : C} (i : A ⟶ B)
    [Mono i] {m : ℕ} (h : m • 𝟙 B = 0) : m • 𝟙 A = 0 := by
  rw [← cancel_mono i, Preadditive.nsmul_comp, Category.id_comp, zero_comp,
    ← Category.comp_id i, ← Preadditive.comp_nsmul, h, comp_zero]

/-- An object killed by `m` has every quotient killed by `m`. -/
theorem nsmul_id_eq_zero_of_epi {C : Type*} [Category C] [Preadditive C] {A B : C} (p : A ⟶ B)
    [Epi p] {m : ℕ} (h : m • 𝟙 A = 0) : m • 𝟙 B = 0 := by
  rw [← cancel_epi p, Preadditive.comp_nsmul, Category.comp_id, comp_zero,
    ← Category.id_comp p, ← Preadditive.nsmul_comp, h, zero_comp]

/-- **A constant sheaf killed by `m` is the constant sheaf of `M / m M`**: the constant sheaf
functor preserves cokernels, and carries multiplication by `m` on `M` to multiplication by `m`
on `M̲`, which is zero. -/
def constantSheafCokernelNsmulIso {X : Scheme.{u}} (M : ModuleCat.{max (u + 1) r} Λ) (m : ℕ)
    (h : m • 𝟙 ((constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M) = 0) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj
        (cokernel (m • 𝟙 M)) ≅
      (constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M :=
  let adj := constantSheafAdj X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)
    (etaleSiteTerminalIsTerminal X)
  haveI : (constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).Additive :=
    adj.left_adjoint_additive
  haveI := adj.leftAdjoint_preservesColimits
  have hz :
      (constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).map (m • 𝟙 M) = 0 := by
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, h]
  PreservesCokernel.iso _ _ ≪≫ cokernelIsoOfEq hz ≪≫ cokernelZeroIsoTarget

/-- The quotient `M / m M`, the cokernel of multiplication by `m`, is killed by `m`. -/
theorem nsmul_eq_zero_cokernel_nsmul (M : ModuleCat.{max (u + 1) r} Λ) (m : ℕ)
    (x : (cokernel (m • 𝟙 M) : ModuleCat.{max (u + 1) r} Λ)) : m • x = 0 := by
  have hs : Function.Surjective (cokernel.π (m • 𝟙 M)) :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  obtain ⟨y, rfl⟩ := hs x
  have h := congrArg (fun φ => φ y) (cokernel.condition (m • 𝟙 M))
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.comp_apply,
    LinearMap.zero_apply] at h
  rw [← map_nsmul, ← h]
  simp

variable [IsNoetherianRing Λ]

/-- **Finiteness of `H^q(Y, j'_! K)` along a filtration of `K` with constant graded pieces.** Let
`j' : T ⟶ Y` be an open immersion and `K` a sheaf of `Λ`-modules on `T_étale` killed by `m`,
with a chain of subobjects from zero to `K` whose successive quotients are constant sheaves of
finite `Λ`-modules. If `H^q(Y, j'_! M̲)` is finite for every finite `Λ`-module `M` killed by `m`,
then `H^q(Y, j'_! K)` is finite. -/
theorem module_finite_cohomology_extensionByZero_of_relSeries {Y T : Scheme.{u}} (j' : T ⟶ Y)
    [IsOpenImmersion j'] (K : EtaleModules.{u, r} Λ T)
    (Xs : RelSeries (ConstantFiniteModuleStep Λ K))
    (h0 : IsZero (Subobject.underlying.obj Xs.head)) (hl : IsIso Xs.last.arrow) (m : ℕ)
    (hK : m • 𝟙 K = 0) (q : ℕ)
    (hM : ∀ M : ModuleCat.{max (u + 1) r} Λ, Module.Finite Λ M → (∀ x : M, m • x = 0) →
      Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ Y).rightDerived q).obj
        ((etaleModuleExtensionByZero.{u, r} Λ j').obj
          ((constantSheaf T.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M)))) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ Y).rightDerived q).obj
      ((etaleModuleExtensionByZero.{u, r} Λ j').obj K)) := by
  let := HasDerivedCategory.standard (EtaleModules.{u, r} Λ Y)
  let := HasDerivedCategory.standard (ModuleCat.{max (u + 1) r} Λ)
  set H := (etaleModuleGlobalSections.{u, r} Λ Y).rightDerived q
  set E := etaleModuleExtensionByZero.{u, r} Λ j'
  have hE : ∀ {A B : EtaleModules.{u, r} Λ T} (e : A ≅ B), Module.Finite Λ (H.obj (E.obj A)) →
      Module.Finite Λ (H.obj (E.obj B)) :=
    fun e h => Module.Finite.equiv (H.mapIso (E.mapIso e)).toLinearEquiv
  have hind : ∀ i : Fin (Xs.length + 1),
      Module.Finite Λ (H.obj (E.obj (Subobject.underlying.obj (Xs i)))) := by
    intro i
    induction i using Fin.induction with
    | zero =>
      have : H.Additive := (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
        (etaleModuleGlobalSections.{u, r} Λ Y)).additive q
      exact module_finite_of_isZero Λ (H.map_isZero (E.map_isZero h0))
    | succ i ih =>
      obtain ⟨hle, M, hMfin, ⟨e⟩⟩ := Xs.step i
      set f := (Xs i.castSucc).ofLE (Xs i.succ) hle
      let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
      have hS : S.ShortExact :=
        { exact := S.exact_of_g_is_cokernel (cokernelIsCokernel f) }
      have hmM : m • 𝟙 ((constantSheaf T.smallEtaleTopology
          (ModuleCat.{max (u + 1) r} Λ)).obj M) = 0 :=
        nsmul_id_eq_zero_of_epi e.hom <| nsmul_id_eq_zero_of_epi (cokernel.π f) <|
          nsmul_id_eq_zero_of_mono (Xs i.succ).arrow hK
      have h₃ : Module.Finite Λ (H.obj (E.obj (cokernel f))) :=
        hE (constantSheafCokernelNsmulIso Λ M m hmM ≪≫ e.symm)
          (hM _ (Module.Finite.of_surjective (cokernel.π (m • 𝟙 M)).hom
            ((ModuleCat.epi_iff_surjective _).1 inferInstance))
            (nsmul_eq_zero_cokernel_nsmul.{u, r} Λ M m))
      exact Stacks.Cohomology.module_finite_cohomology_of_shortExact Y.smallEtaleTopology Λ
        (S.map E) (hS.map_of_exact E) q ih h₃
  exact hE (asIso Xs.last.arrow) (hind (Fin.last _))

end Stacks.EtaleCohomology.TorsionModules

end

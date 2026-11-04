module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.CompactSupportSheafFiniteness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.InverseImageFamilyVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SeparablyClosedFieldSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperFrobeniusLeray

/-!
# `Rf_! G = 0` over a finite field from the vanishing of `Hⁱ_c(X_k̄, G)`

Let `k` be a finite field, `f : X ⟶ Spec k` separated of finite type with a compactification `j`,
`Λ` a finite ring and `G` a sheaf of `Λ`-modules on `X_étale`. If `Hⁱ_c(X_k̄, G) = 0` for every `i`
(`Stacks.EtaleCohomology.compactSupportSheafCohomology`, `k̄` an algebraic closure of `k`), then
`Rf_! G = 0` in `D⁺(Spec k, Λ)`.

Indeed the inverse image to `Spec k̄` of `Rf_! G` is detected by its derived global sections: over
a separably closed field global sections are an equivalence
(`Stacks.EtaleCohomology.isEquivalence_globalSections_of_isSepClosed`), hence exact, so
`H^q(RΓ(Spec k̄, K)) = Γ(H^q K)`, and they reflect zero objects. By Tag 0GK0
(`Stacks.EtaleCohomology.compactlySupportedCohomologyGroupBaseChangeIso`) these derived global
sections compute `H^q_c(X_k̄, G|_{X_k̄})`, which is `Hⁱ_c(X_k̄, G)`. Finally `Spec k̄ ⟶ Spec k` is
surjective, so a complex on `Spec k` whose inverse image vanishes is zero.

This is how the vanishing of the compactly supported cohomology of the Artin–Schreier sheaf
becomes the vanishing of the kernel `Rf_!(M ⊗ L_ψ)` of the Fourier transform.

## Main results

* `Stacks.EtaleCohomology.isZero_of_forall_isZero_homology_etaleModuleDerivedGlobalSections`:
  over a separably closed field, `K = 0` once `H^q(RΓ(Spec Ω, K)) = 0` for all `q`.
* `Stacks.EtaleCohomology.compactSupportSheafCohomologyIsoCompactlySupportedCohomologyGroup`:
  `Hⁱ_c(X_k̄, G) ≅ H^i_c(X_k̄, G|_{X_k̄})`, for any ring of coefficients.
* `Stacks.EtaleCohomology.isZero_derivedLowerShriek_single_of_forall_subsingleton`.

## References

* [Stacks Project, Tag 0GK0](https://stacks.math.columbia.edu/tag/0GK0)
* [Stacks Project, Tag 03QO](https://stacks.math.columbia.edu/tag/03QO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section SepClosed

/-- **Over a separably closed field a bounded below complex with vanishing derived global
sections is zero**: global sections are an equivalence, hence exact, so they commute with
cohomology and reflect zero objects. -/
theorem isZero_of_forall_isZero_homology_etaleModuleDerivedGlobalSections (Λ : Type) [Ring Λ]
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ (Spec (.of Ω))))
    (h : ∀ q : ℤ, IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q).obj
      ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj K))) : IsZero K := by
  have : HasLimitsOfSize.{0, u} (ModuleCat.{u + 1} Λ) := ModuleCat.hasLimitsOfSize.{0, u, u + 1}
  have : HasSheafify (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    hasSheafifyEtale.{u, 0} (Spec (.of Ω)) Λ
  have := isEquivalence_globalSections_of_isSepClosed Ω (ModuleCat.{u + 1} Λ)
  let Γ := etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))
  have hq : ∀ q : ℤ, IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj K) := fun q => by
    have h1 : IsZero (Γ.obj ((DerivedCategory.Plus.homologyFunctor _ q).obj K)) :=
      (h q).of_iso ((Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso Γ q).app K).symm
    rw [IsZero.iff_id_eq_zero]
    exact Γ.map_injective ((Γ.map_id _).trans ((h1.eq_of_src _ _).trans (Γ.map_zero _ _).symm))
  have : IsIso (0 : K ⟶ K) := by
    rw [DerivedCategory.Plus.isIso_iff]
    intro q
    rw [Functor.map_zero]
    exact ⟨0, (hq q).eq_of_src _ _, (hq q).eq_of_src _ _⟩
  rw [IsZero.iff_id_eq_zero, ← IsIso.inv_hom_id (0 : K ⟶ K), comp_zero]

end SepClosed

section Comparison

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar]

/-- **`Hⁱ_c(X_k̄, G)` is the compactly supported cohomology of `G|_{X_k̄}` over `k̄`**, computed
through the base change of the compactification, for any ring of coefficients. -/
def compactSupportSheafCohomologyIsoCompactlySupportedCohomologyGroup
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (G : EtaleModules.{u, 0} Λ X)
    (i : ℤ) :
    (compactSupportSheafCohomology Λ f j kbar i).obj G ≅
      (compactlySupportedCohomologyGroup.{u, 0} kbar (pullback.snd f (specAlgebraMap k kbar))
        (compactificationFieldBaseChange f j kbar) Λ i).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj G)) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).mapIso
    (compactSupportFrobeniusCohomologySingleIso f j kbar G ≪≫
      DerivedCategory.Plus.ι.mapIso ((etaleModuleDerivedGlobalSections.{u, 0} Λ
        (Spec (.of kbar))).mapIso ((etaleModuleDerivedDirectImage.{u, 0} Λ
          (pullback.snd j.toBase (specAlgebraMap k kbar))).mapIso
            ((DerivedCategory.Plus.singleFunctor _ 0).mapIso
              ((compactificationFieldBaseChangeExtensionByZeroIso.{u, 0} Λ f j kbar).app
                G).symm))) ≪≫
      derivedDirectImageSectionsExtensionByZeroIso f j kbar Λ _)

end Comparison

section Vanishing

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [Ring Λ] [Finite Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f))

omit [Fintype k] in
/-- The spectrum of a field extension surjects onto the spectrum of the base field. -/
theorem iUnion_range_specAlgebraMap (kbar : Type u) [Field kbar] [Algebra k kbar] :
    ⋃ _a : PUnit.{u + 1}, Set.range (specAlgebraMap k kbar).base = Set.univ := by
  refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨PUnit.unit, ?_⟩
  obtain ⟨y⟩ : Nonempty (Spec (.of kbar)) := inferInstance
  exact ⟨y, Subsingleton.elim _ _⟩

omit [Fintype k] in
/-- **`Rf_! G = 0` once `Hⁱ_c(X_k̄, G) = 0` for all `i`**, for a sheaf `G` of modules over a finite
ring on a separated scheme of finite type over a finite field: the inverse image of `Rf_! G` to
`Spec k̄` has derived global sections `RΓ_c(X_k̄, G)` (Tag 0GK0), and over `k̄` global sections
detect zero objects. -/
theorem isZero_derivedLowerShriek_single_of_forall_subsingleton (G : EtaleModules.{u, 0} Λ X)
    (h : ∀ i : ℤ, Subsingleton
      ((compactSupportSheafCohomology Λ f j (AlgebraicClosure k) i).obj G)) :
    IsZero ((derivedLowerShriek.{u, 0} f j Λ).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G)) := by
  let kbar := AlgebraicClosure k
  let g := specAlgebraMap k kbar
  let K := (DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X) 0).obj G
  refine isZero_of_forall_isZero_etaleModuleDerivedInverseImagePlus Λ (ι := PUnit.{u + 1})
    (fun _ => g) (iUnion_range_specAlgebraMap (k := k) kbar) _ fun _ => ?_
  refine isZero_of_forall_isZero_homology_etaleModuleDerivedGlobalSections Λ kbar _ fun q => ?_
  have sq : IsPullback (pullback.fst f g) (pullback.snd f g) f g := IsPullback.of_hasPullback f g
  let e₀ := compactlySupportedCohomologyGroupBaseChangeIso Λ sq j K
    (isTorsionPlus_of_finite Λ X K) q
  let e₁ : (etaleModuleDerivedInverseImagePlus.{u, 0} Λ (pullback.fst f g)).obj K ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f g)).obj G) :=
    (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
      (etaleModuleInverseImage.{u, 0} Λ (pullback.fst f g)) 0).app G
  let e₂ := compactSupportSheafCohomologyIsoCompactlySupportedCohomologyGroup Λ f j kbar G q
  let e : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q).obj
      ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ g).obj
          ((derivedLowerShriek.{u, 0} f j Λ).obj K))) ≅
      (compactSupportSheafCohomology Λ f j kbar q).obj G :=
    e₀ ≪≫ (compactlySupportedCohomologyGroup.{u, 0} kbar (pullback.snd f g)
      (j.baseChange sq) Λ q).mapIso e₁ ≪≫ e₂.symm
  have := h q
  exact (ModuleCat.isZero_of_subsingleton _).of_iso e

end Vanishing

end Stacks.EtaleCohomology

end

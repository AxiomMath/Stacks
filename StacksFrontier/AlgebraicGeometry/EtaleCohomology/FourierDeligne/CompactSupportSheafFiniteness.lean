module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveFiniteLevelCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportCompactificationIndependence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Independence

/-!
# Finiteness of `Hⁱ_c(X_k̄, G)` and independence of the compactification, for sheaves

Let `X` be separated of finite type over a finite field `k`, of dimension at most one, `k̄` an
algebraically closed extension of `k`, and `G` a constructible sheaf of `ℤ/m`-modules on `X_étale`.
Then `Hⁱ_c(X_k̄, G)` (`Stacks.EtaleCohomology.compactSupportSheafCohomology`) is finite: it is
`Hⁱ_c` over `k̄` of `G|_{X_k̄}`, constructible on `X_k̄`, which is finite by
[Stacks, Tag 0GKR]. The argument is the one for a level of an `ℓ`-adic sheaf, with a sheaf in
its place.

For a sheaf `G` of `Λ`-modules killed by a positive integer, `Hⁱ_c(X_k̄, G)` computed through two
compactifications `j₁`, `j₂` of `X` are isomorphic: both are isomorphic to `Hⁱ_c(X_k̄, G)` through
a compactification mapping to each ([Stacks, Tag 0ATU];
`Stacks.EtaleCohomology.compactSupportFrobeniusCohomologyHomIso`).

## Main results

* `Stacks.EtaleCohomology.finite_compactSupportSheafCohomology_of_isConstructible`.
* `Stacks.EtaleCohomology.compactSupportSheafCohomologyCompactificationIso`.

## References

* [Stacks Project, Tag 0GKR](https://stacks.math.columbia.edu/tag/0GKR)
* [Stacks Project, Tag 0ATU](https://stacks.math.columbia.edu/tag/0ATU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Finite

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] [Fintype k]
  (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  [IsAlgClosed kbar]

/-- **`Hⁱ_c(X_k̄, G)` is finite** for a constructible sheaf `G` of `ℤ/m`-modules on a scheme of
dimension at most one, separated of finite type over a finite field: [Stacks, Tag 0GKR] for the
restriction of `G` to `X_k̄`. -/
theorem finite_compactSupportSheafCohomology_of_isConstructible
    (hdim : topologicalKrullDim X.1 ≤ 1) (m : ℕ) [NeZero m] (G : EtaleModules.{u, 0} (ZMod m) X.1)
    (hG : IsBigSiteConstructibleEtaleModule B X (ZMod m) G) (i : ℤ) :
    Finite ((compactSupportSheafCohomology (ZMod m) f j kbar i).obj G) := by
  have : CompactSpace X.obj := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X.obj := quasiSeparatedSpace_of_quasiSeparated f
  have : CompactSpace ↥(pullback f (specAlgebraMap k kbar) : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f (specAlgebraMap k kbar))
  have : QuasiSeparatedSpace ↥(pullback f (specAlgebraMap k kbar) : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (specAlgebraMap k kbar))
  let Λ := ZMod m
  let gX := pullback.fst f (specAlgebraMap k kbar)
  obtain ⟨B', hY, hc⟩ := exists_isConstructibleEtaleModule_inverseImage Λ B X gX G hG
  have hdimk : topologicalKrullDim ↥(pullback f (specAlgebraMap k kbar) : Scheme.{u}) ≤ 1 := by
    have h := topologicalKrullDim_pullback_le_of_fiber f 1
      (fun y ↦ (topologicalKrullDim_fiber_of_spec_field k f y).le.trans (by exact_mod_cast hdim))
      (specAlgebraMap k kbar)
    exact_mod_cast h
  have h0 := TorsionModules.module_finite_compactlySupportedCohomologyGroup B' (B'.obj _ hY)
    (pullback.snd f (specAlgebraMap k kbar)) hdimk (compactificationFieldBaseChange f j kbar) Λ
    ((etaleModuleInverseImage.{u, 0} Λ gX).obj G) hc (isTorsionEtaleModule_zmod _ _) i
  let e₁ : (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj G) ≅
      (etaleModuleExtensionByZero.{u, 0} Λ (compactificationFieldBaseChangeImmersion f j kbar)).obj
        ((etaleModuleInverseImage.{u, 0} Λ gX).obj G) :=
    ((compactificationFieldBaseChangeExtensionByZeroIso.{u, 0} Λ f j kbar).app G).symm
  let e₂ : (compactSupportSheafCohomology Λ f j kbar i).obj G ≅
      (compactlySupportedCohomologyGroup.{u, 0} kbar (pullback.snd f (specAlgebraMap k kbar))
        (compactificationFieldBaseChange f j kbar) Λ i).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} Λ gX).obj G)) :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).mapIso
      (compactSupportFrobeniusCohomologySingleIso f j kbar G ≪≫
        DerivedCategory.Plus.ι.mapIso ((etaleModuleDerivedGlobalSections.{u, 0} Λ
          (Spec (.of kbar))).mapIso ((etaleModuleDerivedDirectImage.{u, 0} Λ
            (pullback.snd j.toBase (specAlgebraMap k kbar))).mapIso
              ((DerivedCategory.Plus.singleFunctor _ 0).mapIso e₁))) ≪≫
        derivedDirectImageSectionsExtensionByZeroIso f j kbar Λ _)
  have : Module.Finite Λ ((compactSupportSheafCohomology Λ f j kbar i).obj G) :=
    Module.Finite.equiv e₂.symm.toLinearEquiv
  exact Module.finite_of_finite Λ

end Finite

section Independence

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **`Hⁱ_c(X_k̄, G)` through `j₁` is `Hⁱ_c(X_k̄, G)` through `j₂`**, for a sheaf `G` killed by a
positive integer: both are `Hⁱ_c(X_k̄, G)` through a compactification mapping to `j₁` and to `j₂`
([Stacks, Tag 0ATU]). -/
def compactSupportSheafCohomologyCompactificationIso (j₁ j₂ : CompactificationOf (Over.mk f))
    (G : EtaleModules.{u, 0} Λ X) (m : ℕ) (hm : 0 < m) (h : m • 𝟙 G = 0) (i : ℤ) :
    (compactSupportSheafCohomology Λ f j₁ kbar i).obj G ≅
      (compactSupportSheafCohomology Λ f j₂ kbar i).obj G :=
  let K := (sheafSingleComplex Λ).obj G
  have hK : ∀ n, ∃ m : ℕ, 0 < m ∧ m • 𝟙 (K.obj.X n) = 0 :=
    fun n => ⟨m, hm, nsmul_id_sheafSingleComplex_X G m h n⟩
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).mapIso
    ((compactSupportFrobeniusCohomologyHomIso Λ f (IsCofiltered.minToLeft j₁ j₂) kbar K hK).symm ≪≫
      compactSupportFrobeniusCohomologyHomIso Λ f (IsCofiltered.minToRight j₁ j₂) kbar K hK)

end Independence

end Stacks.EtaleCohomology

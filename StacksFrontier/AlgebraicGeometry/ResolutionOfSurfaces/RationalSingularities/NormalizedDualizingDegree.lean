module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedDualizingTrace
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegreeExtra

/-!
# The degree in which `f^!(ω_A)` can be concentrated

In Situation [Stacks, Tag 0B4W] let `ω_A` be a dualizing module of `A` and write
`K = f^!(ω_A)` for the twisted inverse image of [Stacks, Tag 0A9E] applied to `ω_A` in degree
zero. [Stacks, Remark 0B4R] asserts that `K` is a module `ω_X` placed in degree zero. This file
proves one half of the degree statement: **if `K` is a module placed in degree `n`, then
`n ≤ 0`.**

## Main results

* `nonempty_homSingle_relativeDualizingComplex_equiv`: relative duality in degree zero against a
  quasi-coherent `ℱ` with `H¹(X, ℱ) = 0`, with no hypothesis on `f^!(ω_A)`:
  `Hom(ℱ[0], f^!(ω_A)) ≃ Hom_A(Γ(X, ℱ), ω_A)`.
* `nonempty_homSingle_unit_relativeDualizingComplex_equiv`: at `ℱ = 𝒪_X`,
  `Hom(𝒪_X[0], f^!(ω_A)) ≃ ω_A`.
* `le_zero_of_iso_singleFunctor`: if `f^!(ω_A) ≅ M[-n]` with `ω_A ≠ 0`, then `n ≤ 0`.

## Implementation notes

`Hom(𝒪_X[0], f^!(ω_A))` is `ω_A` by duality, so it is nonzero. If `f^!(ω_A)` were a module placed
in a positive degree `n`, every morphism from `𝒪_X[0]`, an object of `D^{≤ 0}`, to it, an object of
`D^{≥ n} ⊆ D^{≥ 1}`, would vanish by the orthogonality axiom of the canonical t-structure.

## References

* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open Stacks.Duality (isQuasicoherent_homology_derivedPushforward_of_qcqs)
open CategoryTheory CategoryTheory.Limits
open Stacks.Duality (singleQuasiCoherent)
open Stacks.Cohomology.AffineBase (moduleGlobalSections)

universe u

namespace AlgebraicGeometry.RationalSingularitySituation

variable (S : RationalSingularitySituation.{u}) [IsLocallyNoetherian S.X]

omit [IsLocallyNoetherian S.X] in
/-- **Relative duality in degree zero against a quasi-coherent module with vanishing first
cohomology**, with nothing assumed of `f^!(ω_A)`: `Hom(ℱ[0], f^!(ω_A)) ≃ Hom_A(Γ(X, ℱ), ω_A)`. It
is the composite of Grothendieck duality for `Rf_* ⊣ f^!`, the reading of the result in degree zero
(`Rf_*(ℱ[0])` is concentrated there), the comparison `H⁰(Rf_*(ℱ[0])) ≅ f_*ℱ`, and global sections
over the affine base — the four last bijections of `bijective_normalizationPairing`. -/
theorem nonempty_homSingle_relativeDualizingComplex_equiv (ωA : ModuleCat.{u} S.A)
    (F : S.X.Modules) (hF : F.IsQuasicoherent)
    (hH : IsZero (((moduleGlobalSections S.X).rightDerived 1).obj F)) :
    Nonempty (((DerivedCategory.singleFunctor S.X.Modules 0).obj F ⟶
      (S.relativeDualizingComplex ωA).obj) ≃
        (moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward S.f).obj F) ⟶ ωA)) := by
  let : ((Scheme.Modules.pushforward S.f).obj F).IsQuasicoherent :=
    isQuasicoherent_of_iso S.base _ _ (S.derivedPushforwardSingleIso.app F)
      ((isQuasicoherent_homology_derivedPushforward_of_qcqs S.f) (singleQuasiCoherent F hF 0) 0)
  have hι : Function.Bijective ((ObjectProperty.ι _).map
      (X := singleQuasiCoherent F hF 0) (Y := S.relativeDualizingComplex ωA)) :=
    ⟨Functor.map_injective _, Functor.map_surjective _⟩
  have hι' : Function.Bijective ((ObjectProperty.ι _).map
      (X := (Stacks.Duality.quasiCoherentDerivedPushforward S.f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs S.f)).obj (singleQuasiCoherent F hF 0))
      (Y := S.baseDualizingComplex ωA)) :=
    ⟨Functor.map_injective _, Functor.map_surjective _⟩
  have hb3 : Function.Bijective (fun u : (DerivedCategory.singleFunctor S.X.Modules 0).obj F ⟶
      (S.relativeDualizingComplex ωA).obj =>
        (Stacks.Duality.derivedPushforward S.f).map u ≫ S.relativeDualizingTrace ωA) := by
    refine (Function.Bijective.of_comp_iff _ hι).1 ?_
    have hc : (fun u : (DerivedCategory.singleFunctor S.X.Modules 0).obj F ⟶
          (S.relativeDualizingComplex ωA).obj =>
            (Stacks.Duality.derivedPushforward S.f).map u ≫ S.relativeDualizingTrace ωA) ∘
        ((ObjectProperty.ι _).map
          (X := singleQuasiCoherent F hF 0) (Y := S.relativeDualizingComplex ωA)) =
        ((ObjectProperty.ι _).map
          (X := (Stacks.Duality.quasiCoherentDerivedPushforward S.f
            (isQuasicoherent_homology_derivedPushforward_of_qcqs S.f)).obj
              (singleQuasiCoherent F hF 0))
          (Y := S.baseDualizingComplex ωA)) ∘
        ⇑(Stacks.Duality.relativeDualizingComplexHomEquiv S.f
            (isQuasicoherent_homology_derivedPushforward_of_qcqs S.f)
          (S.baseDualizingComplex ωA) (singleQuasiCoherent F hF 0)) :=
      funext fun u => (congrArg (ObjectProperty.ι _).map
        (Stacks.Duality.relativeDualizingComplexHomEquiv_apply S.f
            (isQuasicoherent_homology_derivedPushforward_of_qcqs S.f)
          (S.baseDualizingComplex ωA) (singleQuasiCoherent F hF 0) u)).symm
    exact Eq.mpr (congrArg Function.Bijective hc) (hι'.comp (Equiv.bijective _))
  have hb4 :=
    DerivedCategory.bijective_homologyFunctor_map_comp_singleFunctorCompHomologyFunctorIso
      ((Stacks.Duality.derivedPushforward S.f).obj
        ((DerivedCategory.singleFunctor S.X.Modules 0).obj F)) 0
      (fun j hj => S.isZero_homology_derivedPushforward_single F hF hH j hj)
      ((tilde.functor (CommRingCat.of S.A)).obj ωA)
  have hb5 : Function.Bijective (fun w : (DerivedCategory.homologyFunctor S.base.Modules 0).obj
      ((Stacks.Duality.derivedPushforward S.f).obj
        ((DerivedCategory.singleFunctor S.X.Modules 0).obj F)) ⟶
      (tilde.functor (CommRingCat.of S.A)).obj ωA =>
        (S.derivedPushforwardSingleIso.app F).inv ≫ w) :=
    ⟨fun w w' h => (cancel_epi (S.derivedPushforwardSingleIso.app F).inv).1 h,
      fun v => ⟨(S.derivedPushforwardSingleIso.app F).hom ≫ v, by simp⟩⟩
  have hb6 := bijective_moduleSpecΓFunctor_map (R := CommRingCat.of S.A)
    ((Scheme.Modules.pushforward S.f).obj F) ωA
  exact ⟨Equiv.ofBijective _ (hb6.comp (hb5.comp (hb4.comp hb3)))⟩

/-- **`Hom(𝒪_X[0], f^!(ω_A)) ≃ ω_A`.** Relative duality in degree zero against the structure
sheaf, whose first cohomology vanishes because `A` defines a rational singularity, followed by
`Hom_A(Γ(X, 𝒪_X), ω_A) = ω_A`, as `Γ(X, 𝒪_X) = A` ([Stacks, Tag 0B4Y]). -/
theorem nonempty_homSingle_unit_relativeDualizingComplex_equiv (ωA : ModuleCat.{u} S.A) :
    Nonempty (((DerivedCategory.singleFunctor S.X.Modules 0).obj
      (SheafOfModules.unit S.X.ringCatSheaf) ⟶ (S.relativeDualizingComplex ωA).obj) ≃ ωA) := by
  obtain ⟨Φ⟩ := S.nonempty_homSingle_relativeDualizingComplex_equiv ωA
    (SheafOfModules.unit S.X.ringCatSheaf) (_root_.isQuasicoherent_of_isCoherent _)
    (by
      let := HasDerivedCategory.standard S.X.Modules
      let := HasDerivedCategory.standard (ModuleCat.{u} Γ(S.X, ⊤))
      exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ 1 _).2
        S.isZero_firstCohomologyStructureSheaf)
  exact ⟨Φ.trans (S.unitGlobalSectionsHomEquiv ωA)⟩

/-- **`f^!(ω_A)` is not concentrated in a positive degree.** If `f^!(ω_A) ≅ M[-n]` for an
`𝒪_X`-module `M` and `ω_A ≠ 0`, then `n ≤ 0`: `Hom(𝒪_X[0], f^!(ω_A)) = ω_A` is nonzero, while for
`n > 0` every morphism from the object `𝒪_X[0]` of `D^{≤ 0}` to the object `M[-n]` of
`D^{≥ 1}` vanishes. -/
theorem le_zero_of_iso_singleFunctor (ωA : ModuleCat.{u} S.A) [Nontrivial ωA]
    (M : S.X.Modules) (n : ℤ)
    (e : (S.relativeDualizingComplex ωA).obj ≅
      (DerivedCategory.singleFunctor S.X.Modules n).obj M) :
    n ≤ 0 := by
  by_contra hn
  obtain ⟨Φ⟩ := S.nonempty_homSingle_unit_relativeDualizingComplex_equiv ωA
  have hzero : ∀ u : (DerivedCategory.singleFunctor S.X.Modules 0).obj
      (SheafOfModules.unit S.X.ringCatSheaf) ⟶ (S.relativeDualizingComplex ωA).obj, u = 0 := by
    intro u
    let U : S.X.Modules := SheafOfModules.unit S.X.ringCatSheaf
    have : ((DerivedCategory.singleFunctor S.X.Modules 0).obj U).IsLE 0 := inferInstance
    have : ((DerivedCategory.singleFunctor S.X.Modules n).obj M).IsGE n := inferInstance
    have h : u ≫ e.hom = 0 :=
      DerivedCategory.TStructure.t.zero (u ≫ e.hom) 0 n (by omega)
    rw [← cancel_mono e.hom, h, zero_comp]
  obtain ⟨x, y, hxy⟩ := exists_pair_ne ωA
  exact hxy (Φ.symm.injective ((hzero _).trans (hzero _).symm))

end AlgebraicGeometry.RationalSingularitySituation

end

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.RingTheory.Fitting.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Fitting ideal sheaves

The Fitting ideals of a module over a commutative ring form an increasing chain of ideals.
Applied to the modules of sections of a sheaf of modules on a scheme, they cut out a
decreasing chain of closed subschemes: the *Fitting stratification*.

## Main definitions

* `Stacks.Morphisms.pushforwardStructureSheaf` is `f_* 𝒪_X`, regarded as an `𝒪_S`-module.
* `Stacks.Fitting.idealSheaf` is the largest ideal sheaf whose ideal on each affine open is
  below the Fitting ideal of the sections there.

## Main results

* `Stacks.Fitting.fittingIdeal_monotone` says the Fitting ideals of a finite module increase.
* `Stacks.Fitting.idealSheaf_monotone` says the Fitting ideal sheaves increase, so that the
  closed subschemes they cut out decrease.
* `Stacks.Fitting.idealSheaf_pushforward_zero` says that the zeroth Fitting ideal sheaf of
  `f_* 𝒪_X` vanishes as soon as `f` admits a section: the first closed subscheme of the
  Fitting stratification is the whole base.
* `Stacks.Fitting.fittingIdeal_map_basicOpen` says that, for a finite `f`, the Fitting ideals
  of the sections of `f_* 𝒪_X` commute with restriction to a basic open.
* `Stacks.Fitting.ideal_idealSheaf_pushforward` concludes that for a finite `f` the Fitting
  ideal sheaf is cut out by exactly those ideals.
* `Stacks.Fitting.exists_notMem_support_idealSheaf_pushforward` says no point of the base lies
  on every member of the stratification.

## Implementation notes

`idealSheaf` is `Scheme.IdealSheafData.ofIdeals` applied to the family of module-theoretic
Fitting ideals of the sections, with the convention that the family is zero on an affine open
whose sections do not form a finite module (the Fitting ideals are only defined for finite
modules). Because `ofIdeals` is the *largest* ideal sheaf below a family, only the inequality
`Stacks.Fitting.ideal_idealSheaf_le` holds in general; the reverse inequality needs the family
to be compatible with localization. That compatibility is proved here for `f_* 𝒪_X` with `f`
finite, where it does not need quasi-coherence of `f_* 𝒪_X`: the preimage of an affine open is
affine, the sections over a basic open are the corresponding ring localization, and the
module-theoretic Fitting ideals commute with that base change by Stacks Tag 07ZA. The
localization is transported from `IsLocalization` to `IsLocalizedModule` over the base ring by
`isLocalizedModule_iff_isLocalization`, whose middle algebra is the sections of `𝒪_X` over the
preimage.

`Stacks.Morphisms.pushforwardStructureSheaf` is Stacks Tag 02KA's `f_* 𝒪_X`. It is declared
here, rather than in a Chapter 29 file, because this is its only consumer.

## References

* [Stacks Project, Tag 07Z9](https://stacks.math.columbia.edu/tag/07Z9)
* [Stacks Project, Tag 07Z7](https://stacks.math.columbia.edu/tag/07Z7)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 0C3D](https://stacks.math.columbia.edu/tag/0C3D)
* [Stacks Project, Tag 05P8](https://stacks.math.columbia.edu/tag/05P8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace Stacks.Morphisms

/-- The direct image `f_* 𝒪_X`, regarded as a sheaf of `𝒪_S`-modules. -/
@[ega "0 4.2.1" "case F = A", ega "II 1.1.1" "partial"]
noncomputable abbrev pushforwardStructureSheaf {X S : Scheme.{u}} (f : X ⟶ S) : S.Modules :=
  (Scheme.Modules.pushforward f).obj (SheafOfModules.unit _)

/-- A morphism of schemes with a section induces an injection on sections over every open. -/
theorem app_injective_of_section {X S : Scheme.{u}} (f : X ⟶ S) (e : S ⟶ X)
    (he : e ≫ f = 𝟙 S) (U : S.Opens) : Function.Injective (f.app U).hom := by
  have h : IsIso ((e ≫ f).app U) := by
    rw [Scheme.Hom.congr_app he U]
    infer_instance
  have h' : Function.Injective (f.app U ≫ e.app (f ⁻¹ᵁ U)).hom :=
    (ConcreteCategory.bijective_of_isIso ((e ≫ f).app U)).1
  intro x y hxy
  exact h' (by simp only [CommRingCat.comp_apply, hxy])

/-- If `f` admits a section, then `f_* 𝒪_X` is a faithful module over the structure sheaf:
no nonzero section of `𝒪_S` annihilates it. -/
theorem annihilator_pushforwardStructureSheaf_eq_bot {X S : Scheme.{u}} (f : X ⟶ S) (e : S ⟶ X)
    (he : e ≫ f = 𝟙 S) (U : S.Opens) :
    Module.annihilator Γ(S, U) Γ(pushforwardStructureSheaf f, U) = (⊥ : Ideal Γ(S, U)) := by
  rw [eq_bot_iff]
  intro a ha
  rw [Module.mem_annihilator] at ha
  have h2 : (f.app U).hom a * 1 = 0 :=
    ha (show Γ(pushforwardStructureSheaf f, U) from (1 : Γ(X, f ⁻¹ᵁ U)))
  have h3 : (f.app U).hom a = (f.app U).hom 0 := by simpa using h2
  simpa using app_injective_of_section f e he U h3

/-- The sections of `f_* 𝒪_X` over an affine open form a finite module when `f` is finite. -/
instance module_finite_pushforwardStructureSheaf {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
    (U : S.affineOpens) :
    Module.Finite Γ(S, U.1) Γ(pushforwardStructureSheaf f, U.1) :=
  IsFinite.finite_app f U.1 U.2

/-- The previous instance, in the shape typeclass search needs on a basic open: the open
`S.basicOpen a` does not expose the `S.affineOpens` it is a basic open of. -/
instance module_finite_pushforwardStructureSheaf_basicOpen {X S : Scheme.{u}} (f : X ⟶ S)
    [IsFinite f] {U : S.affineOpens} (a : Γ(S, U.1)) :
    Module.Finite Γ(S, S.basicOpen a) Γ(pushforwardStructureSheaf f, S.basicOpen a) :=
  module_finite_pushforwardStructureSheaf f (S.affineBasicOpen a)

end Stacks.Morphisms

namespace Stacks.Fitting

open scoped Classical in
/-- The `k`-th Fitting ideal sheaf of a sheaf of modules on a scheme: the largest ideal sheaf
whose ideal on each affine open is below the Fitting ideal of the module of sections there. -/
@[sga "7 VI 5.2" "more general"]
noncomputable def idealSheaf {X : Scheme.{u}} (F : X.Modules) (k : ℤ) : X.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals fun U ↦
    if h : Module.Finite Γ(X, U.1) Γ(F, U.1) then
      letI := h
      fittingIdeal (M := Γ(F, U.1)) k
    else ⊥

/-- The Fitting ideal sheaf is below any ideal that bounds the Fitting ideal of the sections
whenever these form a finite module. -/
private theorem ideal_idealSheaf_le_of {X : Scheme.{u}} (F : X.Modules) (k : ℤ)
    (U : X.affineOpens) (I : Ideal Γ(X, U.1))
    (h : ∀ hf : Module.Finite Γ(X, U.1) Γ(F, U.1),
      (letI := hf; fittingIdeal (M := Γ(F, U.1)) k) ≤ I) :
    (idealSheaf F k).ideal U ≤ I := by
  refine (Scheme.IdealSheafData.ideal_ofIdeals_le _ U).trans ?_
  by_cases hf : Module.Finite Γ(X, U.1) Γ(F, U.1)
  · rw [dite_eq_left hf]
    exact h hf
  · rw [dite_eq_right hf]
    exact bot_le

open scoped Classical in
/-- On an affine open whose sections form a finite module, the Fitting ideal sheaf is below the
module-theoretic Fitting ideal of the sections. -/
theorem ideal_idealSheaf_le {X : Scheme.{u}} (F : X.Modules) (k : ℤ) (U : X.affineOpens)
    [h : Module.Finite Γ(X, U.1) Γ(F, U.1)] :
    (idealSheaf F k).ideal U ≤ fittingIdeal (M := Γ(F, U.1)) k :=
  ideal_idealSheaf_le_of F k U _ fun _ ↦ le_rfl

/-- **Stacks Project, Tag 05P8.** The Fitting ideal sheaves increase, so the closed subschemes
they cut out form a decreasing chain. -/
@[stacks 05P8 "decreasing closed subschemes"]
theorem idealSheaf_monotone {X : Scheme.{u}} (F : X.Modules) : Monotone (idealSheaf F) := by
  intro a b hab
  refine Scheme.IdealSheafData.ofIdeals_mono fun U ↦ ?_
  split_ifs with h
  · exact fittingIdeal_monotone hab
  · exact le_rfl

/-- The zeroth Fitting ideal sheaf of `f_* 𝒪_X` vanishes as soon as `f` admits a section: the
section makes `𝒪_S` a direct summand of `f_* 𝒪_X`, so the module of sections is faithful and
its zeroth Fitting ideal, which annihilates it, is zero. -/
theorem idealSheaf_pushforward_zero {X S : Scheme.{u}} (f : X ⟶ S) (e : S ⟶ X)
    (he : e ≫ f = 𝟙 S) : idealSheaf (Morphisms.pushforwardStructureSheaf f) 0 = ⊥ := by
  refine le_antisymm (fun U ↦ ideal_idealSheaf_le_of _ _ U _ fun _ ↦ ?_) bot_le
  refine le_trans ?_ (Morphisms.annihilator_pushforwardStructureSheaf_eq_bot f e he U.1).le
  exact (fittingIdeal_basic_properties.{u, u, u, u}
    (R := Γ(S, U.1)) (M := Γ(Morphisms.pushforwardStructureSheaf f, U.1))).2.2.2.2.2.1

/-! ### The Fitting ideals of a finite pushforward form an ideal sheaf -/

open Opposite in
/-- For a finite morphism `f`, the Fitting ideals of the sections of `f_* 𝒪_X` are compatible
with localization: the sections over a basic open are a localization of the sections over the
affine open, and Fitting ideals commute with that base change. -/
theorem fittingIdeal_map_basicOpen {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
    (U : S.affineOpens) (a : Γ(S, U.1)) (k : ℕ) :
    Ideal.map (S.presheaf.map (homOfLE (S.basicOpen_le a)).op).hom
        (fittingIdeal (M := Γ(Morphisms.pushforwardStructureSheaf f, U.1)) (k : ℤ)) =
      fittingIdeal (M := Γ(Morphisms.pushforwardStructureSheaf f, S.basicOpen a)) (k : ℤ) := by
  let _ : Algebra Γ(S, U.1) Γ(X, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
  let _ : Algebra Γ(S, S.basicOpen a) Γ(X, f ⁻¹ᵁ S.basicOpen a) :=
    (f.app (S.basicOpen a)).hom.toAlgebra
  let _ : Algebra Γ(X, f ⁻¹ᵁ U.1) Γ(X, f ⁻¹ᵁ S.basicOpen a) :=
    (X.presheaf.map (homOfLE (f.preimage_mono (S.basicOpen_le a))).op).hom.toAlgebra
  let _ : Algebra Γ(S, U.1) Γ(X, f ⁻¹ᵁ S.basicOpen a) :=
    (S.presheaf.map (homOfLE (S.basicOpen_le a)).op ≫ f.app (S.basicOpen a)).hom.toAlgebra
  have htower1 : IsScalarTower Γ(S, U.1) Γ(S, S.basicOpen a) Γ(X, f ⁻¹ᵁ S.basicOpen a) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have htower2 : IsScalarTower Γ(S, U.1) Γ(X, f ⁻¹ᵁ U.1) Γ(X, f ⁻¹ᵁ S.basicOpen a) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp]
    congr 1
    exact f.naturality (homOfLE (S.basicOpen_le a)).op
  have hfinU : Module.Finite Γ(S, U.1) Γ(X, f ⁻¹ᵁ U.1) :=
    Morphisms.module_finite_pushforwardStructureSheaf f U
  have hfinV : Module.Finite Γ(S, S.basicOpen a) Γ(X, f ⁻¹ᵁ S.basicOpen a) :=
    Morphisms.module_finite_pushforwardStructureSheaf_basicOpen f a
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid Γ(X, f ⁻¹ᵁ U.1) (Submonoid.powers a))
      Γ(X, f ⁻¹ᵁ S.basicOpen a) := by
    rw [Algebra.algebraMapSubmonoid_powers, RingHom.algebraMap_toAlgebra]
    exact (U.2.preimage f).isLocalization_of_eq_basicOpen _ _ (f.preimage_basicOpen a)
  have hlm : IsLocalizedModule (Submonoid.powers a)
      (IsScalarTower.toAlgHom Γ(S, U.1) Γ(X, f ⁻¹ᵁ U.1) Γ(X, f ⁻¹ᵁ S.basicOpen a)).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr hloc
  have hal := U.2.isLocalization_basicOpen a
  have hbc := IsLocalizedModule.isBaseChange (Submonoid.powers a) Γ(S, S.basicOpen a)
    (IsScalarTower.toAlgHom Γ(S, U.1) Γ(X, f ⁻¹ᵁ U.1) Γ(X, f ⁻¹ᵁ S.basicOpen a)).toLinearMap
  have hfinT : Module.Finite Γ(S, S.basicOpen a)
      (TensorProduct Γ(S, U.1) Γ(S, S.basicOpen a) Γ(X, f ⁻¹ᵁ U.1)) :=
    Module.Finite.equiv hbc.equiv.symm
  have hbase := (fittingIdeal_basic_properties.{u, u, u, u}
    (R := Γ(S, U.1)) (M := Γ(X, f ⁻¹ᵁ U.1))).2.2.1 Γ(S, S.basicOpen a) k
  exact hbase.symm.trans (fittingIdeal_eq_of_linearEquiv hbc.equiv k)

/-- For a finite morphism, the Fitting ideals of the sections of `f_* 𝒪_X` are an ideal sheaf,
not merely a family of ideals. -/
noncomputable def pushforwardIdealSheafData {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] (k : ℤ) :
    S.IdealSheafData where
  ideal U := fittingIdeal (M := Γ(Morphisms.pushforwardStructureSheaf f, U.1)) k
  map_ideal_basicOpen U a := by
    rcases lt_or_ge k 0 with hk | hk
    · rw [fittingIdeal, ite_eq_left_of_eq_true _ _ (eq_true hk), Ideal.map_bot, fittingIdeal,
        ite_eq_left_of_eq_true _ _ (eq_true hk)]
      rfl
    · lift k to ℕ using hk
      exact fittingIdeal_map_basicOpen f U a k

open scoped Classical in
/-- For a finite morphism, the Fitting ideal sheaf of `f_* 𝒪_X` is cut out by exactly the
Fitting ideals of the sections, with no shrinking from `ofIdeals`. -/
theorem idealSheaf_pushforward_eq {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] (k : ℤ) :
    idealSheaf (Morphisms.pushforwardStructureSheaf f) k = pushforwardIdealSheafData f k := by
  rw [idealSheaf]
  conv_rhs => rw [← Scheme.IdealSheafData.ofIdeals_ideal (pushforwardIdealSheafData f k)]
  congr 1
  funext U
  exact dite_eq_left (Morphisms.module_finite_pushforwardStructureSheaf f U)

/-- **Stacks Project, Tag 0C3D** for a finite pushforward: on every affine open the Fitting
ideal sheaf of `f_* 𝒪_X` is the module-theoretic Fitting ideal of the sections. -/
theorem ideal_idealSheaf_pushforward {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] (k : ℤ)
    (U : S.affineOpens) :
    (idealSheaf (Morphisms.pushforwardStructureSheaf f) k).ideal U =
      fittingIdeal (M := Γ(Morphisms.pushforwardStructureSheaf f, U.1)) k := by
  rw [idealSheaf_pushforward_eq]
  rfl

/-- No point of the base lies on every member of the Fitting stratification of a finite
morphism: near any point the sections of `f_* 𝒪_X` are generated by finitely many elements,
and from that index on the Fitting ideal is the unit ideal. -/
theorem exists_notMem_support_idealSheaf_pushforward {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
    (x : S) :
    ∃ n : ℕ, x ∉ (idealSheaf (Morphisms.pushforwardStructureSheaf f) (n : ℤ)).support := by
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have := Morphisms.module_finite_pushforwardStructureSheaf f ⟨U, hU⟩
  obtain ⟨n, g, hg⟩ :=
    Module.Finite.exists_fin (R := Γ(S, U)) (M := Γ(Morphisms.pushforwardStructureSheaf f, U))
  refine ⟨n, ?_⟩
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU,
    ideal_idealSheaf_pushforward f (n : ℤ) ⟨U, hU⟩,
    (fittingIdeal_basic_properties.{u, u, u, u}
      (R := Γ(S, U)) (M := Γ(Morphisms.pushforwardStructureSheaf f, U))).1 n ⟨g, hg⟩,
    Submodule.top_coe, Scheme.zeroLocus_univ]
  simpa using hxU

end Stacks.Fitting

end

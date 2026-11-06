module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Ext.Baer
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Injective dimension under coextension of scalars

Let `f : R →+* S` be a ring homomorphism and let `Y` be an `R`-module. Coextension of
scalars sends `Y` to the `S`-module `Hom_R(S, Y)`, where `S` is regarded as an `R`-module
along `f`; in Mathlib this is `ModuleCat.coextendScalars f`.

This file proves the classical change-of-rings theorem of Rees: if `Y` has injective
dimension at most `d` over `R` and the higher Ext groups `Ext_R^{q+1}(S, Y)` all vanish,
then `Hom_R(S, Y)` has injective dimension at most `d` over `S`.

## Main results

* `ModuleCat.hasInjectiveDimensionLE_coextendScalars`: the statement above.

## Proof idea

Induction on `d`, generalizing `Y`.

For `d = 0` the hypothesis says that `Y` is injective, and `coextendScalars f` is right
adjoint to the (exact, hence monomorphism preserving) functor `restrictScalars f`, so it
takes injective objects to injective objects.

For the inductive step, choose an injective presentation `0 → Y → J → C → 0` of `Y`.
Dimension shifting gives that `C` has injective dimension at most `d`, and the long exact
sequence for `Ext_R(S, -)` together with the injectivity of `J` shows that the higher Ext
groups `Ext_R^{q+1}(S, C)` vanish as well, so the induction hypothesis applies to `C`.
Since `coextendScalars f` is a right adjoint it preserves kernels, so applying it to the
presentation yields a sequence of `S`-modules which is exact except possibly on the right;
surjectivity of `Hom_R(S, J) → Hom_R(S, C)` is exactly the statement that every map
`S → C` of `R`-modules lifts along `J → C`, which again follows from the long exact
sequence and the vanishing of `Ext_R^1(S, Y)`. Dimension shifting in the other direction
for the resulting short exact sequence of `S`-modules finishes the induction.

## Implementation notes

The hypothesis on the Ext groups is phrased as `Subsingleton (Abelian.Ext _ _ (q + 1))`,
which is how vanishing of Ext is spelled in Mathlib; the `HasExt` instance for
`ModuleCat.{u} R` with `R : Type u` is available because that category is locally
`u`-small.

Exactness of the coextended sequence is obtained from
`CategoryTheory.ShortComplex.Exact.map_of_mono_of_preservesKernel`, which needs only that
the functor preserves the relevant kernel; this avoids having to know that
`coextendScalars f` is exact (it is not, in general).
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace ModuleCat

open Abelian Limits

/-- If `T` is a short exact sequence in an abelian category and `Ext X T.X₁ 1` vanishes,
then every morphism `X ⟶ T.X₃` lifts along `T.g`. -/
private lemma exists_comp_eq_of_subsingleton_ext {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] {T : ShortComplex C} (hT : T.ShortExact) (X : C)
    [Subsingleton (Ext.{w} X T.X₁ 1)] (u : X ⟶ T.X₃) :
    ∃ v : X ⟶ T.X₂, v ≫ T.g = u := by
  obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ X hT (Ext.mk₀ u) (n₁ := 1) rfl
    (by subsingleton)
  refine ⟨Ext.homEquiv₀ x₂, (Ext.mk₀_bijective _ _).1 ?_⟩
  rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply]
  exact hx₂

/-- Coextension of scalars is a right adjoint, hence preserves finite limits. -/
private noncomputable instance preservesFiniteLimitsCoextendScalars
    {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    PreservesFiniteLimits (coextendScalars.{u, u, u} f) := by
  have := (restrictCoextendScalarsAdj.{u, u, u} f).rightAdjoint_preservesLimits
  infer_instance

/-- If every `R`-linear map `S → N` factors through `g : M ⟶ N`, then the induced map
`Hom_R(S, M) ⟶ Hom_R(S, N)` of `S`-modules is an epimorphism. -/
private lemma epi_coextendScalars_map {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    {M N : ModuleCat.{u} R} (g : M ⟶ N)
    (h : ∀ u : (restrictScalars.{u, u, u} f).obj (of S S) ⟶ N, ∃ v : _ ⟶ M, v ≫ g = u) :
    Epi ((coextendScalars.{u, u, u} f).map g) := by
  refine (ModuleCat.epi_iff_surjective _).2 fun y ↦ ?_
  obtain ⟨v, hv⟩ := h (homEquiv.symm (CoextendScalars.equiv f N y))
  refine ⟨(CoextendScalars.equiv f M).symm v.hom, CoextendScalars.ext (LinearMap.ext fun s ↦ ?_)⟩
  exact congr($(hv).hom s)

/-- Rees' change-of-rings theorem: if the `R`-module `Y` has injective dimension at most
`d` and the Ext groups `Ext_R^{q+1}(S, Y)` vanish for all `q`, where `S` is viewed as an
`R`-module along `f : R →+* S`, then the coinduced `S`-module `Hom_R(S, Y)` has injective
dimension at most `d`. -/
public theorem hasInjectiveDimensionLE_coextendScalars
    {R S : Type u} [Ring R] [Ring S] (f : R →+* S) (d : ℕ) (Y : ModuleCat.{u} R)
    (hY : HasInjectiveDimensionLE Y d)
    (hExt : ∀ q : ℕ, Subsingleton
      (Abelian.Ext ((ModuleCat.restrictScalars.{u, u, u} f).obj (ModuleCat.of S S)) Y (q + 1))) :
    HasInjectiveDimensionLE ((ModuleCat.coextendScalars.{u, u, u} f).obj Y) d := by
  induction d generalizing Y with
  | zero =>
    rw [← injective_iff_hasInjectiveDimensionLE_zero] at hY ⊢
    exact Injective.injective_of_adjoint (restrictCoextendScalarsAdj.{u, u, u} f) Y
  | succ d ih =>
    let ip : InjectivePresentation Y := Classical.arbitrary _
    have hS : ip.shortComplex.ShortExact := ip.shortExact_shortComplex
    have hmono := hS.mono_f
    have h₃ : HasInjectiveDimensionLE ip.shortComplex.X₃ d :=
      (hS.hasInjectiveDimensionLT_X₃_iff d inferInstance).mpr hY
    have hExt₃ : ∀ q : ℕ, Subsingleton (Ext
        ((restrictScalars.{u, u, u} f).obj (of S S)) ip.shortComplex.X₃ (q + 1)) := by
      intro q
      have := Ext.subsingleton_of_injective
        ((restrictScalars.{u, u, u} f).obj (of S S)) ip.shortComplex.X₂ q
      refine subsingleton_of_forall_eq 0 fun x₃ ↦ ?_
      obtain ⟨x₂, rfl⟩ := Ext.covariant_sequence_exact₃ _ hS x₃ (n₁ := q + 1 + 1) rfl
        (by have := hExt (q + 1); subsingleton)
      rw [show x₂ = 0 from Subsingleton.elim _ _, Ext.zero_comp]
    have hepi : Epi ((coextendScalars.{u, u, u} f).map ip.shortComplex.g) :=
      have := hExt 0
      epi_coextendScalars_map f _ fun u ↦ exists_comp_eq_of_subsingleton_ext hS _ u
    have hmono' : Mono ((coextendScalars.{u, u, u} f).map ip.shortComplex.f) := inferInstance
    have hS' : (ip.shortComplex.map (coextendScalars.{u, u, u} f)).ShortExact :=
      { exact := ShortComplex.Exact.map_of_mono_of_preservesKernel hS.exact _ hmono inferInstance
        mono_f := hmono'
        epi_g := hepi }
    have hinj : Injective ((coextendScalars.{u, u, u} f).obj ip.shortComplex.X₂) :=
      Injective.injective_of_adjoint (restrictCoextendScalarsAdj.{u, u, u} f) _
    rw [injective_iff_hasInjectiveDimensionLE_zero] at hinj
    exact hS'.hasInjectiveDimensionLT_X₁ (d + 1) (ih _ h₃ hExt₃)
      (hasInjectiveDimensionLT_of_ge
        ((coextendScalars.{u, u, u} f).obj ip.shortComplex.X₂) 1 (d + 2) (by lia))

end ModuleCat

end

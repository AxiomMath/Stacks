module

public import StacksFrontier.AlgebraicGeometry.NilpotentThickeningLift.Glue
public import StacksFrontier.AlgebraicGeometry.NormInvertible.PullbackGenerator
public import StacksFrontier.AlgebraicGeometry.NormInvertible.Reconstruction
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Lifting a power of a section across a surjective closed immersion

Let `i : Z ⟶ X` be a closed immersion which is surjective on points, with `X` quasi-separated,
and let `L` be an invertible `𝒪_X`-module. For a global section `t` of `(i^* L)^{⊗ n}`, `n ≥ 1`,
whose nonvanishing locus lies over an affine open of `X` on which `L` is trivial, there is a
global section `s` of a positive tensor power of `L` with `i⁻¹(X_s) = Z_t`.

The section is built in charts. On an affine open `U_j` trivializing `L` by `g_j`, the section
`t` is `τ_j (i^* g_j)^{⊗ n}`; lifting `τ_j` to `f_j ∈ Γ(U_j, 𝒪_X)` gives local lifts whose
differences `f_j - c_{jk}^n f_k` vanish on `Z`, hence are nilpotent because `i` is onto. The
gluing of `Stacks.NilpotentThickeningLift.exists_sections_nonvanishingOpen_eq` then produces `s`.

## Main results

* `Stacks.NilpotentThickeningLift.isNilpotent_of_app_eq_zero`: a function on a quasi-compact open
  of `X` vanishing on `Z` is nilpotent.
* `Stacks.NilpotentThickeningLift.exists_sections_preimage_nonvanishingOpen_eq`: the lift.

## References

* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace RingedSpaceModuleAdjunction

universe u

namespace Stacks.NilpotentThickeningLift

open Stacks.SheafOfModules Stacks.SheafOfModules.Invertible

variable {Z X : Scheme.{u}} (i : Z ⟶ X)

local notation "rs" => AlgebraicGeometry.sectionsRestrict

/-- Taking inverse images of opens along a surjective morphism is injective. -/
theorem preimage_injective (hsurj : Function.Surjective i.base) {A B : X.Opens}
    (h : i ⁻¹ᵁ A = i ⁻¹ᵁ B) : A = B :=
  Opens.ext (Set.preimage_injective.mpr hsurj (congrArg (fun V : Z.Opens => (V : Set Z)) h))

/-- The map on functions of a morphism of schemes commutes with restriction. -/
theorem app_rs {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    i.app V (rs h a) = rs (Scheme.Hom.preimage_mono i h) (i.app U a) :=
  congrArg (fun φ => φ.hom a) (i.naturality (homOfLE h).op)

/-- **A function on a quasi-compact open vanishing on `Z` is nilpotent**, for `i` surjective. -/
theorem isNilpotent_of_app_eq_zero (hsurj : Function.Surjective i.base) {V : X.Opens}
    (hV : IsCompact (V : Set X)) (a : Γ(X, V)) (ha : i.app V a = 0) : IsNilpotent a := by
  refine (Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact hV a).mpr ?_
  refine preimage_injective i hsurj ?_
  rw [Scheme.preimage_basicOpen, ha, Scheme.basicOpen_zero]
  rfl

variable (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- **The pulled-back frames of `(i^* L)^{⊗ n}` differ by the pulled-back transition function.**
For generators `g` on `U` and `g'` on `V` with `g' = c • g` on `U ∩ V`, the generators
`(i^* g')^{⊗ n}` and `(i^* g)^{⊗ n}` of `(i^* L)^{⊗ n}` over `i⁻¹(U ∩ V)` differ by
`(i^♯ c)^n`. -/
theorem pullbackTensorPowerGenerator_restrict_spec {U V : X.Opens}
    (g : GeneratorSections X.toRingedSpace L U) (g' : GeneratorSections X.toRingedSpace L V)
    (n : ℕ) :
    (generatorRestrict (tensorPowerModule' ((modulePullback i.toLRSHom.toShHom).obj L) (n : ℤ))
        (Scheme.Hom.preimage_mono i (inf_le_right : U ⊓ V ≤ V))
        (tensorPowerGenerator _ (pullbackGenerator i L (isInvertible_of_tensorInvertible L) V g')
          n)).val =
      i.app (U ⊓ V) (transitionFn L g g') ^ n •
        (generatorRestrict (tensorPowerModule' ((modulePullback i.toLRSHom.toShHom).obj L) (n : ℤ))
          (Scheme.Hom.preimage_mono i (inf_le_left : U ⊓ V ≤ U))
          (tensorPowerGenerator _ (pullbackGenerator i L (isInvertible_of_tensorInvertible L) U g)
            n)).val := by
  set hL := isInvertible_of_tensorInvertible L
  set M := (modulePullback i.toLRSHom.toShHom).obj L
  have key : ∀ {W : X.Opens} (h : U ⊓ V ≤ W) (g : GeneratorSections X.toRingedSpace L W),
      (generatorRestrict (tensorPowerModule' M (n : ℤ)) (Scheme.Hom.preimage_mono i h)
        (tensorPowerGenerator _ (pullbackGenerator i L hL W g) n)).val =
      (tensorPowerGenerator M (pullbackGenerator i L hL (U ⊓ V) (generatorRestrict L h g))
        n).val := fun h g => by
    have e := tensorPowerGenerator_restrict M (Scheme.Hom.preimage_mono i h)
      (pullbackGenerator i L hL _ g) n
    rw [pullbackGenerator_restrict i L hL h g] at e
    exact congrArg Subtype.val e
  rw [key inf_le_right g', key inf_le_left g]
  have hr := generatorRatioUnit_tensorPowerGenerator M (i ⁻¹ᵁ (U ⊓ V))
    (pullbackGenerator i L hL (U ⊓ V) (generatorRestrict L inf_le_left g))
    (pullbackGenerator i L hL (U ⊓ V) (generatorRestrict L inf_le_right g')) n
  rw [generatorRatioUnit_pullbackGenerator] at hr
  have h' : generatorRatio (tensorPowerModule' M (n : ℤ)) (i ⁻¹ᵁ (U ⊓ V))
      (tensorPowerGenerator M (pullbackGenerator i L hL (U ⊓ V)
        (generatorRestrict L inf_le_left g)) n)
      (tensorPowerGenerator M (pullbackGenerator i L hL (U ⊓ V)
        (generatorRestrict L inf_le_right g')) n) = i.app (U ⊓ V) (transitionFn L g g') ^ n :=
    ((generatorRatioUnit_val _ _ _ _).symm.trans (congrArg Units.val hr)).trans
      ((Units.val_pow_eq_pow_val _ n).trans
        (congrArg (· ^ n) ((Units.coe_map _ _).trans
          (congrArg _ (generatorRatioUnit_val _ _ _ _)))))
  have hs := generatorRatio_spec (tensorPowerModule' M (n : ℤ)) (i ⁻¹ᵁ (U ⊓ V))
    (tensorPowerGenerator M (pullbackGenerator i L hL (U ⊓ V)
      (generatorRestrict L inf_le_left g)) n)
    (tensorPowerGenerator M (pullbackGenerator i L hL (U ⊓ V)
      (generatorRestrict L inf_le_right g')) n)
  rw [h'] at hs
  exact hs

/-- **Lifting a power of a section across a surjective closed immersion.** Let `i : Z ⟶ X` be a
closed immersion surjective on points, with `X` quasi-separated, and let `g_j` be generators of
`L` on a finite affine open cover `U_j` of `X`. For a global section `t` of `(i^* L)^{⊗ n}`,
`n ≥ 1`, with `Z_t ⊆ i⁻¹(U_{j₀})`, there is a global section `s` of a positive tensor power of `L`
with `i⁻¹(X_s) = Z_t`. -/
theorem exists_sections_preimage_nonvanishingOpen_eq [IsClosedImmersion i]
    (hsurj : Function.Surjective i.base) [QuasiSeparatedSpace X]
    {J : Type u} [Finite J] (U : J → X.Opens) (hU : ∀ j, IsAffineOpen (U j))
    (hcov : ∀ x, ∃ j, x ∈ U j) (g : ∀ j, GeneratorSections X.toRingedSpace L (U j)) (j₀ : J)
    (n : ℕ) (hn : 1 ≤ n)
    (t : (tensorPowerModule' ((modulePullback i.toLRSHom.toShHom).obj L) (n : ℤ)).sections)
    (ht : Stacks.SheafOfModules.nonvanishingOpen (X := Z.toRingedSpace) _ t ≤ i ⁻¹ᵁ U j₀) :
    ∃ D : ℕ, 1 ≤ D ∧ ∃ s : (tensorPowerModule' L (D : ℤ)).sections,
      i ⁻¹ᵁ Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) _ s =
        Stacks.SheafOfModules.nonvanishingOpen (X := Z.toRingedSpace) _ t := by
  set hL := isInvertible_of_tensorInvertible L
  set M := (modulePullback i.toLRSHom.toShHom).obj L
  set γ : ∀ j, GeneratorSections Z.toRingedSpace (tensorPowerModule' M (n : ℤ)) (i ⁻¹ᵁ U j) :=
    fun j => tensorPowerGenerator M (pullbackGenerator i L hL (U j) (g j)) n with hγ
  have hτ : ∀ j, ∃ τ : Γ(Z, i ⁻¹ᵁ U j), t.eval (op (i ⁻¹ᵁ U j)) = τ • (γ j).val := fun j =>
    ((bijective_smul_generator _ (γ j)).surjective (t.eval (op (i ⁻¹ᵁ U j)))).imp
      fun _ h => h.symm
  choose τ hτ using hτ
  choose f hf using fun j => i.app_surjective (U j) (hU j) (τ j)
  have hZ : ∀ j, Z.basicOpen (τ j) =
      Stacks.SheafOfModules.nonvanishingOpen (X := Z.toRingedSpace) _ t ⊓ i ⁻¹ᵁ U j := fun j =>
    AlgebraicGeometry.Scheme.Modules.basicOpen_eq_inf_nonvanishingOpen_of_generator M t (γ j)
      (τ j) (hτ j)
  have hpre : ∀ j, i ⁻¹ᵁ X.basicOpen (f j) =
      Stacks.SheafOfModules.nonvanishingOpen (X := Z.toRingedSpace) _ t ⊓ i ⁻¹ᵁ U j := fun j => by
    rw [Scheme.preimage_basicOpen, hf j, hZ j]
  have hWpre : i ⁻¹ᵁ X.basicOpen (f j₀) =
      Stacks.SheafOfModules.nonvanishingOpen (X := Z.toRingedSpace) _ t := by
    rw [hpre j₀]; exact inf_eq_left.mpr ht
  have hfW : ∀ j, X.basicOpen (f j) = X.basicOpen (f j₀) ⊓ U j := fun j =>
    preimage_injective i hsurj (by rw [hpre j, Scheme.Hom.preimage_inf, hWpre])
  have hcoord : ∀ j k, rs (Scheme.Hom.preimage_mono i (inf_le_left : U j ⊓ U k ≤ U j)) (τ j) =
      i.app (U j ⊓ U k) (transitionFn L (g j) (g k)) ^ n *
        rs (Scheme.Hom.preimage_mono i (inf_le_right : U j ⊓ U k ≤ U k)) (τ k) := by
    intro j k
    have hres : ∀ l (h : i ⁻¹ᵁ (U j ⊓ U k) ≤ i ⁻¹ᵁ U l),
        t.eval (op (i ⁻¹ᵁ (U j ⊓ U k))) =
          rs h (τ l) • (generatorRestrict (tensorPowerModule' M (n : ℤ)) h (γ l)).val := by
      intro l h
      refine (PresheafOfModules.sections_property t (homOfLE h).op).symm.trans ?_
      exact (congrArg (fun z => (tensorPowerModule' M (n : ℤ)).val.map (homOfLE h).op z)
        (hτ l)).trans (PresheafOfModules.map_smul _ (homOfLE h).op _ _)
    have e := (hres j (Scheme.Hom.preimage_mono i inf_le_left)).symm.trans
      (hres k (Scheme.Hom.preimage_mono i inf_le_right))
    rw [pullbackTensorPowerGenerator_restrict_spec i L (g j) (g k) n, smul_smul] at e
    refine (bijective_smul_generator _
      (generatorRestrict (tensorPowerModule' M (n : ℤ))
        (Scheme.Hom.preimage_mono i (inf_le_left : U j ⊓ U k ≤ U j)) (γ j))).injective ?_
    refine e.trans ?_
    exact congrArg (fun r => r • (generatorRestrict (tensorPowerModule' M (n : ℤ))
        (Scheme.Hom.preimage_mono i (inf_le_left : U j ⊓ U k ≤ U j)) (γ j)).val)
      (mul_comm (G := Γ(Z, i ⁻¹ᵁ (U j ⊓ U k))) _ _)
  have hcpt : ∀ j k, IsCompact ((U j ⊓ U k : X.Opens) : Set X) := fun j k =>
    (hU j).isCompact.inter_of_isOpen (hU k).isCompact (U j).isOpen (U k).isOpen
  have hnil : ∀ j, IsNilpotent (rs inf_le_left (f j) -
      transitionFn L (g j) (g j₀) ^ n * rs inf_le_right (f j₀)) := by
    intro j
    refine isNilpotent_of_app_eq_zero i hsurj (hcpt j j₀) _ ?_
    rw [map_sub, map_mul, map_pow, app_rs, app_rs, hf, hf, hcoord j j₀, sub_self]
  obtain ⟨D, hD, s, hs⟩ := exists_sections_nonvanishingOpen_eq L U g n f (X.basicOpen (f j₀)) j₀
    hU hcov hn (X.basicOpen_le _) hfW hnil
  exact ⟨D, hD, s, by rw [hs, hWpre]⟩

end Stacks.NilpotentThickeningLift

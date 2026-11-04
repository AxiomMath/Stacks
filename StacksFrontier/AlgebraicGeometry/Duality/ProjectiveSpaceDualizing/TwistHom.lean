module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpaceDualizing.StructureSheafHom
public import StacksFrontier.AlgebraicGeometry.SheafInternalHom.Basic
public import StacksFrontier.AlgebraicGeometry.TensorPowers.Basic
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingIso

/-!
# Morphisms between shifted twists on projective space

Let `S` be a scheme, let `n = m + 1 ≥ 1` and let `ℙⁿ_S` be projective `n`-space over `S`. For
integers `i`, `j` with `-n ≤ j - i ≤ -1` and any degrees `a`, `b`, every morphism

  `𝒪(i)[a] ⟶ 𝒪(j)[b]`

in `D(𝒪_{ℙⁿ_S})` is zero. This is the vanishing
`Hom_{D(𝒪_X)}(𝒪_X(i), 𝒪_X(-n-1)[n+p]) = H^p(X, 𝒪_X(-n-1-i)) = 0` of the proof of
[Stacks, Tag 0A9W] for `i ∈ {-n, …, -1}`.

## The argument

Tensoring with the invertible module `𝒪(-i)` is an exact autoequivalence of the category of
`𝒪_{ℙⁿ_S}`-modules, so it induces an autoequivalence of `D(𝒪_{ℙⁿ_S})` commuting with the single
functors, and it carries `𝒪(i)` to `𝒪(0) ≅ 𝒪` and `𝒪(j)` to `𝒪(j - i)`. Morphisms
`𝒪[a] ⟶ 𝒪(j - i)[b]` are seen by `Rf_*`
(`Stacks.Duality.ProjectiveSpaceDualizing.bijective_derivedPushforward_map_unit`), and
`Rf_*(𝒪(j - i)[b]) = 0` because `𝒪(j - i)` lies in the acyclic band
(`Stacks.Duality.ProjectiveSpaceDualizing.isZero_derivedPushforward_twistOver`).

## Main results

* `Stacks.Duality.ProjectiveSpaceDualizing.subsingleton_hom_single_unit_twistOver`: morphisms
  `𝒪[a] ⟶ 𝒪(d)[b]` vanish for `-n ≤ d ≤ -1`.
* `Stacks.Duality.ProjectiveSpaceDualizing.subsingleton_hom_single_twistOver`: **morphisms
  `𝒪(i)[a] ⟶ 𝒪(j)[b]` vanish for `-n ≤ j - i ≤ -1`.**

## Implementation notes

The monoidal structure on `𝒪_X`-modules is `Stacks.SheafInternalHom.schemeMonoidalCategory`,
installed locally; its tensor product is the sheafified tensor product
`Stacks.RelativeVeryAmple.tensorModules` in which the multiplication isomorphisms
`Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOverMulIso` are stated.

## References

* [Stacks Project, Tag 0A9W](https://stacks.math.columbia.edu/tag/0A9W)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver twistZeroIsoUnit twistOverMulIso)

universe u

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory

namespace Stacks.Duality.ProjectiveSpaceDualizing

variable (m : ℕ) (S : Scheme.{u})

/-- **Morphisms `𝒪[a] ⟶ 𝒪(d)[b]` vanish for `-n ≤ d ≤ -1`**: for `n = m + 1` and `d` with
`-n ≤ d < 0`, there is at most one morphism `𝒪[a] ⟶ 𝒪(d)[b]` in `D(𝒪_{ℙⁿ_S})`. -/
theorem subsingleton_hom_single_unit_twistOver {d : ℤ} (hd₁ : -((m + 1 : ℕ) : ℤ) ≤ d)
    (hd₂ : d < 0) (a b : ℤ) :
    Subsingleton ((DerivedCategory.singleFunctor (projectiveSpaceOver (m + 1) S).Modules a).obj
        (SheafOfModules.unit (projectiveSpaceOver (m + 1) S).ringCatSheaf) ⟶
      (DerivedCategory.singleFunctor (projectiveSpaceOver (m + 1) S).Modules b).obj
        (twistOver (m + 1) S d)) :=
  ⟨fun _ _ => (bijective_derivedPushforward_map_unit m S a _).1
    ((isZero_derivedPushforward_twistOver m S hd₁ hd₂ b).eq_of_tgt _ _)⟩

/-- Tensoring with a twist is an autoequivalence of the category of `𝒪_{ℙⁿ_S}`-modules: the twists
are invertible. -/
theorem isEquivalence_tensorLeft_twistOver (e : ℤ) :
    (tensorLeft (twistOver (m + 1) S e)).IsEquivalence :=
  (AlgebraicGeometry.SheafOfModules.isInvertible_iff_isEquivalence_tensorLeft
    (projectiveSpaceOver (m + 1) S).presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf _) _).mp inferInstance

/-- **Morphisms `𝒪(i)[a] ⟶ 𝒪(j)[b]` vanish for `-n ≤ j - i ≤ -1`**: for `n = m + 1` and `i`, `j`
with `-n ≤ j - i < 0`, there is at most one morphism `𝒪(i)[a] ⟶ 𝒪(j)[b]` in `D(𝒪_{ℙⁿ_S})`. -/
theorem subsingleton_hom_single_twistOver {i j : ℤ} (h₁ : -((m + 1 : ℕ) : ℤ) ≤ j - i)
    (h₂ : j - i < 0) (a b : ℤ) :
    Subsingleton ((DerivedCategory.singleFunctor (projectiveSpaceOver (m + 1) S).Modules a).obj
        (twistOver (m + 1) S i) ⟶
      (DerivedCategory.singleFunctor (projectiveSpaceOver (m + 1) S).Modules b).obj
        (twistOver (m + 1) S j)) := by
  let T := tensorLeft (twistOver (m + 1) S (-i))
  have := isEquivalence_tensorLeft_twistOver m S (-i)
  have : T.Additive := T.additive_of_preserves_binary_products
  have : T.asEquivalence.inverse.Additive :=
    T.asEquivalence.inverse.additive_of_preserves_binary_products
  have : T.mapDerivedCategory.IsEquivalence :=
    StacksDraft.DerivedRingIso.isEquivalence_mapDerivedCategory T T.asEquivalence.inverse
      T.asEquivalence.unitIso T.asEquivalence.counitIso
  let eT : ∀ (c d : ℤ), T.mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor _ c).obj (twistOver (m + 1) S d)) ≅
        (DerivedCategory.singleFunctor _ c).obj (twistOver (m + 1) S (-i + d)) := fun c d =>
    (T.mapDerivedCategorySingleFunctor c).app _ ≪≫
      (DerivedCategory.singleFunctor _ c).mapIso
        (AlgebraicGeometry.SheafOfModules.tensorIso (projectiveSpaceOver (m + 1) S).presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf _) _ _ ≪≫
        twistOverMulIso (m + 1) S (-i) d)
  have hsub := subsingleton_hom_single_unit_twistOver m S (d := -i + j) (by omega) (by omega) a b
  refine ⟨fun s t => T.mapDerivedCategory.map_injective ?_⟩
  refine (cancel_epi (eT a i).inv).1 ((cancel_mono (eT b j).hom).1 ?_)
  have e0 : (DerivedCategory.singleFunctor (projectiveSpaceOver (m + 1) S).Modules a).obj
      (twistOver (m + 1) S (-i + i)) ≅ (DerivedCategory.singleFunctor _ a).obj
        (SheafOfModules.unit (projectiveSpaceOver (m + 1) S).ringCatSheaf) :=
    (DerivedCategory.singleFunctor _ a).mapIso
      (eqToIso (congrArg (twistOver (m + 1) S) (by omega)) ≪≫ twistZeroIsoUnit (m + 1) S)
  exact (cancel_epi e0.inv).1 (Subsingleton.elim _ _)

end Stacks.Duality.ProjectiveSpaceDualizing

end

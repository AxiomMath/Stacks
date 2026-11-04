module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartRatioPullbackLocalMulCocycle

/-!
# Reading a section on a nested pair of opens: `restrictPowSection` against `pullSection`

Let `T` be a scheme, `M` an invertible `𝒪_T`-module and `W' ≤ W` two opens of `T`, and write
`j : W' ⟶ W` for the inclusion.  A section `y` of `M^{⊗ n}` over `W` can be read as a global
section of a tensor power on the open subscheme `W'` in two ways:

* restrict `y` to `W'` and read it there —
  `Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection` at `W'`, landing in
  `(M|_{W'})^{⊗ n}`;
* read `y` on `W` and pull the result back along `j` —
  `Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullSection`, landing in `(j^*(M|_W))^{⊗ n}`.

**This file proves the two agree**, across the comparison `M|_{W'} ≅ j^*(M|_W)`.

That is the hypothesis `hχ` of
`Stacks.AlgebraicGeometry.RelativeProjFromSections.resLE_relativeChart_of_iso`, instantiated at
the [Stacks, Tag 01NK] data that a global `(ℒ, ψ)` of [Stacks, Tag 01O8] induces over two nested
opens `Z ≤ V` of the base: the values of `ψ` over `f^{-1}(Z)` are the restrictions of its values
over `f^{-1}(V)` (`…GradedPowerMap.value_res`), so the agreement of the two readings is exactly
the statement that the datum over `Z` is the datum over `V` pulled back.  It is therefore the last
step of the consistency of clause (3) of [Stacks, Tag 01O9] along a nested pair of opens.

## Main definitions

* `…ProjChartRatioPullbackLocalMul.restrictCompIso`: the comparison `M|_{W'} ≅ j^*(M|_W)`, the
  composition law of the inverse image transported along `AlgebraicGeometry.Scheme.homOfLE_ι`.

## Main results

* `…ProjChartRatioPullbackLocalMul.pullbackNatTensorPowIso_inv_congr`: the comparison of the
  tensor powers commutes with the transport of the inverse image along an equality of morphisms.
* `…ProjChartRatioPullbackLocalMul.natTensorPowCongr_restrictPowSection_res`: **the two readings
  agree.**

## The two halves of the proof

The left-hand reading is reduced in three steps: `restrictPowSection_eq'` writes it against
`pullbackNatTensorPowIso`, `AlgebraicGeometry.pullbackSectionHom_map` replaces the restriction of
`y` to `W'` by `y` itself over `W`, and `pullbackSectionHom_congr` replaces the inclusion `W'.ι`
by the composite `j ≫ W.ι`; `pullbackNatTensorPowIso_inv_congr` then moves the resulting transport
out through the comparison of the powers.

The right-hand reading is the composition law in two layers: on sections it is
`pullbackSectionHom_comp_of_le`, the composition law for a section over an **arbitrary** open, and
on the comparisons of the tensor powers it is
`…ProjTripleFunctorLaws.pullbackCompIso_comp_pullbackNatTensorPowIso_inv`, with
`AlgebraicGeometry.Scheme.Modules.pullbackSection_naturality` moving the comparison past the
pullback of a section.

The two halves are joined by the multiplicativity of
`Stacks.AmplePullbackPart1.natTensorPowCongr` in the isomorphism —
`natTensorPowCongr_trans` and `natTensorPowCongr_symm` — which is what makes `restrictCompIso`
a composite of the two transports the halves produce, so that both cancel.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01O8](https://stacks.math.columbia.edu/tag/01O8)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.TensorPowers (natTensorPow)
open Stacks.AmplePullbackPart1 (natTensorPowCongr)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullbackNatTensorPowIso pullSection)
open Stacks.TensorSheafSpellingIso (pullbackCompIso)
open Stacks.NonvanishingLocusRestrict (top_le_ι_preimage_self)

universe u

namespace Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {T : Scheme.{u}} (M : T.Modules) [Stacks.Ample.IsInvertibleModule T M]

/-- **The comparison of the tensor powers commutes with the transport along an equality of
morphisms.**  Pulling back along `k'` and comparing is pulling back along `k`, comparing, and
transporting the result by the `n`-th tensor power of the transport. -/
public theorem pullbackNatTensorPowIso_inv_congr {T' : Scheme.{u}} {k k' : T' ⟶ T} (e : k = k')
    (n : ℕ) (z : Γ((Scheme.Modules.pullback k).obj (natTensorPow M n), ⊤)) :
    Scheme.Modules.Hom.app (pullbackNatTensorPowIso k' M n).inv ⊤
        (Scheme.Modules.Hom.app
          ((Scheme.Modules.pullbackCongr e).hom.app (natTensorPow M n)) ⊤ z)
      = Scheme.Modules.Hom.app
          (natTensorPowCongr ((Scheme.Modules.pullbackCongr e).app M) n).hom ⊤
          (Scheme.Modules.Hom.app (pullbackNatTensorPowIso k M n).inv ⊤ z) := by
  subst e
  have h1 : (Scheme.Modules.pullbackCongr (rfl : k = k)).app M = Iso.refl _ := rfl
  rw [h1, Stacks.AmplePullbackPart1.natTensorPowCongr_refl]
  rfl

variable {W' W : T.Opens} (h : W' ≤ W)

/-- **The comparison `M|_{W'} ≅ j^*(M|_W)`** for the inclusion `j : W' ⟶ W` of a nested pair of
opens: the composition law `j^*(W.ι)^* ≅ (j ≫ W.ι)^*` of the inverse image, transported along
`AlgebraicGeometry.Scheme.homOfLE_ι`, which says that `j ≫ W.ι` is the inclusion of `W'`. -/
public def restrictCompIso :
    (Scheme.Modules.pullback W'.ι).obj M
      ≅ (Scheme.Modules.pullback (T.homOfLE h)).obj ((Scheme.Modules.pullback W.ι).obj M) :=
  ((Scheme.Modules.pullbackCongr (T.homOfLE_ι h)).app M).symm
    ≪≫ ((pullbackCompIso (T.homOfLE h) W.ι).app M).symm

/-- **The two readings of a section over `W` as a global section on a smaller open subscheme
`W'` agree.**  Restricting `y` to `W'` and reading it there is reading it on `W` and pulling the
result back along the inclusion `j : W' ⟶ W`, across the comparison `restrictCompIso`.

This is the hypothesis `hχ` of
`Stacks.AlgebraicGeometry.RelativeProjFromSections.resLE_relativeChart_of_iso` at the
[Stacks, Tag 01NK] data induced by a global `(ℒ, ψ)` over a nested pair of opens of the base, and
so the last step of the consistency of clause (3) of [Stacks, Tag 01O9] along such a pair. -/
public theorem natTensorPowCongr_restrictPowSection_res (n : ℕ) (y : Γ(natTensorPow M n, W)) :
    Scheme.Modules.Hom.app (natTensorPowCongr (restrictCompIso M h) n).hom ⊤
        (restrictPowSection M W' n ((natTensorPow M n).presheaf.map (homOfLE h).op y))
      = pullSection (T.homOfLE h) ((Scheme.Modules.pullback W.ι).obj M) n
          (restrictPowSection M W n y) := by
  have e : T.homOfLE h ≫ W.ι = W'.ι := T.homOfLE_ι h
  have h₃ : (⊤ : W'.toScheme.Opens) ≤ W'.ι ⁻¹ᵁ W :=
    le_trans (le_of_eq (W'.ι_preimage_self).symm) (W'.ι.preimage_mono h)
  have h₂ : (⊤ : W'.toScheme.Opens) ≤ (T.homOfLE h ≫ W.ι) ⁻¹ᵁ W := by rw [e]; exact h₃
  have hstar2 : restrictPowSection M W' n ((natTensorPow M n).presheaf.map (homOfLE h).op y)
      = Scheme.Modules.Hom.app
          (natTensorPowCongr ((Scheme.Modules.pullbackCongr e).app M) n).hom ⊤
          (Scheme.Modules.Hom.app
            (pullbackNatTensorPowIso (T.homOfLE h ≫ W.ι) M n).inv ⊤
            (pullbackSectionHom (T.homOfLE h ≫ W.ι) (natTensorPow M n) W ⊤ h₂ y)) := by
    rw [restrictPowSection_eq']
    refine Eq.trans (congrArg _ ?_) (pullbackNatTensorPowIso_inv_congr M e n _)
    exact (pullbackSectionHom_map W'.ι (natTensorPow M n) W W' h ⊤ _ h₃ y).trans
      (pullbackSectionHom_congr (natTensorPow M n) W e ⊤ h₂ y)
  have hco := (Iso.eq_inv_comp
      ((pullbackCompIso (T.homOfLE h) W.ι).app (natTensorPow M n))).mpr
    (Stacks.AlgebraicGeometry.ProjTripleFunctorLaws.pullbackCompIso_comp_pullbackNatTensorPowIso_inv
      (T.homOfLE h) W.ι M n)
  have hstar1 : Scheme.Modules.Hom.app
        (pullbackNatTensorPowIso (T.homOfLE h ≫ W.ι) M n).inv ⊤
        (pullbackSectionHom (T.homOfLE h ≫ W.ι) (natTensorPow M n) W ⊤ h₂ y)
      = Scheme.Modules.Hom.app
          (natTensorPowCongr ((pullbackCompIso (T.homOfLE h) W.ι).app M) n).hom ⊤
          (pullSection (T.homOfLE h) ((Scheme.Modules.pullback W.ι).obj M) n
            (restrictPowSection M W n y)) := by
    rw [hco]
    simp only [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]
    rw [restrictPowSection_eq']
    refine congrArg _ (congrArg _ ?_)
    exact Eq.trans
      (congrArg _ (pullbackSectionHom_comp_of_le (T.homOfLE h) W.ι (natTensorPow M n) W
        (top_le_ι_preimage_self W) h₂ y).symm)
      (Scheme.Modules.pullbackSection_naturality (T.homOfLE h)
        (pullbackNatTensorPowIso W.ι M n).inv ⊤ ⊤ (by simp) _)
  rw [hstar2, hstar1, restrictCompIso,
    Stacks.AmplePullbackPart1.natTensorPowCongr_trans,
    Stacks.AmplePullbackPart1.natTensorPowCongr_symm,
    Stacks.AmplePullbackPart1.natTensorPowCongr_symm]
  have hc : ∀ {X : Scheme.{u}} {A B : X.Modules} (φ : A ≅ B) (z : Γ(A, ⊤)),
      Scheme.Modules.Hom.app φ.inv ⊤ (Scheme.Modules.Hom.app φ.hom ⊤ z) = z := by
    intro X A B φ z
    rw [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, φ.hom_inv_id]
    rfl
  simp only [Iso.trans_hom, Iso.symm_hom, Scheme.Modules.Hom.comp_app,
    CategoryTheory.comp_apply]
  exact Eq.trans
    (congrArg _ (hc (natTensorPowCongr ((Scheme.Modules.pullbackCongr e).app M) n) _))
    (hc (natTensorPowCongr ((pullbackCompIso (T.homOfLE h) W.ι).app M) n) _)

end Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul

end

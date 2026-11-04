module

public import StacksFrontier.AlgebraicGeometry.AmpleNonvanishing.TwistedSectionChart
public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.SectionProduct.MulSecFormulaLeft

/-!
# A twisted global section of the cycles whose class is nonzero

`Stacks.AmpleNonvanishingChart.exists_twistedSection_restrict_eq_tensorSection` runs the chart
argument of [Stacks, Tag 0BQR] on a nonzero quasi-coherent *module*. This file runs it on the
**cycles** of a complex of quasi-coherent modules, which is what the derived statement of the tag
needs: the output is a global section `ρ` of `Z^p(H) ⊗ L^{⊗ m}` whose image under
`H.homologyπ p ▷ L^{⊗ m}` — its *class* in `H^p(H) ⊗ L^{⊗ m}` — is nonzero.

This is the route recorded in the "A simplification the source does not take" section of
`StacksFrontier/AlgebraicGeometry/AmpleNonvanishing/TwistedSectionChart.lean`: extending a section of
the cycles rather than of `F^p` removes the second application of [Stacks, Tag 01PW] — the global
annihilator — from the critical path, because a global section of `Z^p ⊗ L^{⊗ m}` is already
killed by the differential.

## Main results

* `Stacks.AmpleNonvanishingChart.isQuasicoherent_cycles` and
  `Stacks.AmpleNonvanishingChart.isQuasicoherent_homology`: the cycles and the cohomology sheaves
  of a complex of quasi-coherent `𝒪_X`-modules are quasi-coherent, by the weak Serre class
  `Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerreClass`.
* `Stacks.AmpleNonvanishingChart.exists_twistedCycleSection_class_ne_zero`: **the cocycle of
  [Stacks, Tag 0BQR] as a global section.** For `L` ample invertible and `H` a complex of
  quasi-coherent `𝒪_X`-modules with `H^p(H) ≠ 0`, there are `m` and a global section `ρ` of
  `Z^p(H) ⊗ L^{⊗ m}` whose class in `H^p(H) ⊗ L^{⊗ m}` is nonzero.

## Implementation notes

The five steps are the source's. A nonzero cohomology sheaf has a point with nonzero stalk; the
point lies in an affine chart `X_s` of ampleness; a quasi-coherent module with a nonzero stalk at
a point of an affine open has a nonzero section there; that section of `H^p(H)` lifts to a section
of `Z^p(H)` over the chart, because `Γ(X_s, -)` is exact on quasi-coherent modules
(`Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen`, [Stacks, Tag 01EU]) and
`HomologicalComplex.homologyπ` is an epimorphism; and the surjectivity half of
[Stacks, Tag 01PW] extends its product with a nonvanishing section of a power of `L` to a global
section. That the class of the result is nonzero is the whiskered clause 2 of [Stacks, Tag 01CY],
`Stacks.SectionProduct.eq_zero_of_tensorSection_eq_zero`, together with the compatibility of the
section-level tensor product with a map in its **first** variable,
`Stacks.SectionTensorFormula.tensorSection_whiskerRight`.

**Why the last step is a `calc` of `exact`s and not a `rw`.** Rewriting with
`Stacks.SectionTensorFormula.tensorSection_whiskerRight` fails in *both* directions, reporting a
pattern that unifies with the goal term by term. The two differ only in which
`MonoidalCategory` instance the `▷` and the `tensorSection` carry, which `rw` compares at
reducible transparency and `exact` compares at default transparency. So each step below is an
`exact` of a term whose own type fixes the spelling, chained with `Eq.trans` and `congrArg`; this
is the technique of `StacksFrontier/AlgebraicGeometry/SectionProduct/MulSecFormula.lean`, whose
implementation notes record the same phenomenon for `rw [Category.assoc]`.

## What is not done

The final assembly of [Stacks, Tag 0BQR] — composing this file's `ρ` with
`Stacks.AmpleNonvanishing.unitHomOfGlobalSection`,
`Stacks.TensorSheafSpellingIso.monoidalTensorSheafTensorIso` and
`Stacks.AmpleNonvanishing.termwiseTwistCyclesIso` to produce the cocycle that
`Stacks.AmpleNonvanishing.not_isZero_hypercohomology_derivedTensorSingle_of_cycleHom` consumes —
is **not** carried out. Every mathematical input is present and verified; what blocks it is the
following spelling fact.

`AlgebraicGeometry.Scheme.Modules` and `SheafOfModules X.ringCatSheaf` are `rfl`-equal types with
different instance provenance. `Preadditive (SheafOfModules R)` is a *global* instance, whereas
`Preadditive X.Modules` exists only as the *local* instance
`Stacks.SectionRingGeometric.schemePreadditive`. Re-seating that local instance with
`attribute [local instance]` is **not** sufficient: for `M : X.Modules` the numeral `0` of
`(𝒪_X ⟶ M)` is still rejected, as `OfNat (SheafOfModules.unit X.ringCatSheaf ⟶ M) 0`, and
ascribing the *object* `M` to the other spelling does not move the morphism type — the `Category`
instance is taken from the declared type of `M`, not from the ascription. For the same reason
`rw [← Stacks.AmpleNonvanishing.termwiseTwistCyclesIso_hom_homologyπ]` fails against a goal whose
`≫` was elaborated at the `X.Modules` instance.

The fix is to state the whole chain at `Stacks.DerivedTensor.RingedSite.Modules X.sheaf`, the
spelling with global instances and the one `Stacks.AmpleNonvanishing.termwiseTwist` and the derived
tensor product are already stated at: re-state
`Stacks.AmpleNonvanishing.unitHomOfGlobalSection` and
`Stacks.AmpleNonvanishing.unitHomOfGlobalSection_comp` with their module variable *declared* at
that spelling, rather than ascribing at the use site.

## References

* [Stacks Project, Tag 0BQR](https://stacks.math.columbia.edu/tag/0BQR)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01EU](https://stacks.math.columbia.edu/tag/01EU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MonoidalCategory
open Stacks.Ample Stacks.NonvanishingOpen
open Stacks.SectionExtension (resTop)
open Stacks.SectionTensorFormula (tensorSection)

universe u

namespace Stacks.AmpleNonvanishingChart

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

/-! ### Quasi-coherence of the cycles and of the cohomology sheaves -/

/-- **The cycles of a complex of quasi-coherent `𝒪_X`-modules are quasi-coherent.** They are a
kernel of a map between two terms of the complex, and quasi-coherent modules form a weak Serre
class. -/
theorem isQuasicoherent_cycles (X : Scheme.{u}) (H : CochainComplex X.Modules ℤ)
    (hH : ∀ i : ℤ, (H.X i).IsQuasicoherent) (i : ℤ) : (H.cycles i).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isLimit_kernelFork
    (H.cyclesIsKernel i ((ComplexShape.up ℤ).next i) rfl) (hH i) (hH _)

/-- **The cohomology sheaves of a complex of quasi-coherent `𝒪_X`-modules are quasi-coherent.**
They are a cokernel out of a term of the complex into the cycles, which are quasi-coherent by
`Stacks.AmpleNonvanishingChart.isQuasicoherent_cycles`. -/
theorem isQuasicoherent_homology (X : Scheme.{u}) (H : CochainComplex X.Modules ℤ)
    (hH : ∀ i : ℤ, (H.X i).IsQuasicoherent) (i : ℤ) : (H.homology i).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isColimit_cokernelCofork
    (H.homologyIsCokernel ((ComplexShape.up ℤ).prev i) i rfl) (hH _)
    (isQuasicoherent_cycles X H hH i)

/-! ### The chart step on the cycles -/

/-- **The cocycle of [Stacks, Tag 0BQR] as a global section of the twisted cycles.** Let `L` be an
ample invertible `𝒪_X`-module and `H` a cochain complex of quasi-coherent `𝒪_X`-modules whose
`p`-th cohomology sheaf is nonzero. Then there are an exponent `m` and a global section `ρ` of
`Z^p(H) ⊗ L^{⊗ m}` whose class in `H^p(H) ⊗ L^{⊗ m}` — its image under
`H.homologyπ p ▷ L^{⊗ m}` — is nonzero. -/
theorem exists_twistedCycleSection_class_ne_zero {X : Scheme.{u}} (L : X.Modules)
    [IsInvertibleModule X L] (hL : IsAmple X L) (H : CochainComplex X.Modules ℤ)
    (hH : ∀ i : ℤ, (H.X i).IsQuasicoherent) (p : ℤ) (hHp : ¬ IsZero (H.homology p)) :
    ∃ (m : ℕ) (ρ : Γ(H.cycles p ⊗ tensorPowModule X L (m : ℤ), ⊤)),
      Scheme.Modules.Hom.app (H.homologyπ p ▷ tensorPowModule X L (m : ℤ)) ⊤ ρ ≠ 0 := by
  have hqh : (H.homology p).IsQuasicoherent := isQuasicoherent_homology X H hH p
  have hqz : (H.cycles p).IsQuasicoherent := isQuasicoherent_cycles X H hH p
  obtain ⟨x, hx⟩ := exists_point_not_isZero_stalk (H.homology p) hHp
  obtain ⟨n, hn, s, haff, hxs⟩ :=
    Stacks.AmpleTheory.IsAmple.exists_affine_nonvanishingOpen X L hL x
  obtain ⟨t, ht⟩ := exists_section_ne_zero_of_isAffineOpen (H.homology p) _ haff x hxs hx
  obtain ⟨τ, hτ⟩ := Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen X
    (H.homologyπ p) (Stacks.AmpleTheory.powNonvanishingOpen X L n s) haff t
  have hτ' : Scheme.Modules.Hom.app (H.homologyπ p)
      (Stacks.AmpleTheory.powNonvanishingOpen X L n s) τ = t := hτ
  obtain ⟨m, σ, ρ, hopen, heq⟩ :=
    Stacks.ModuleSectionExtension.exists_tensorPow_tensorSection_of_isAmple L hL
      (H.cycles p) hn s τ
  refine ⟨m, ρ, fun hzero => ht ?_⟩
  refine Stacks.SectionProduct.eq_zero_of_tensorSection_eq_zero (H.homology p)
    (tensorPowModule X L (m : ℤ)) σ (fun y hy => ?_) ?_
  · rw [hopen] at hy
    exact hy
  · have hnat : (H.homology p ⊗ tensorPowModule X L (m : ℤ)).presheaf.map
        (homOfLE (le_top :
          Stacks.AmpleTheory.powNonvanishingOpen X L n s ≤ ⊤)).op
          (Scheme.Modules.Hom.app
            (H.homologyπ p ▷ tensorPowModule X L (m : ℤ)) ⊤ ρ) =
        Scheme.Modules.Hom.app (H.homologyπ p ▷ tensorPowModule X L (m : ℤ))
          (Stacks.AmpleTheory.powNonvanishingOpen X L n s)
          (resTop (Stacks.AmpleTheory.powNonvanishingOpen X L n s) ρ) :=
      (PresheafOfModules.naturality_apply
        (H.homologyπ p ▷ tensorPowModule X L (m : ℤ)).val
        (homOfLE (le_top :
          Stacks.AmpleTheory.powNonvanishingOpen X L n s ≤ ⊤)).op ρ).symm
    calc tensorSection (H.homology p) (tensorPowModule X L (m : ℤ)) t
            (resTop (Stacks.AmpleTheory.powNonvanishingOpen X L n s) σ)
        = Scheme.Modules.Hom.app (H.homologyπ p ▷ tensorPowModule X L (m : ℤ))
              (Stacks.AmpleTheory.powNonvanishingOpen X L n s)
              (tensorSection (H.cycles p) (tensorPowModule X L (m : ℤ)) τ
                (resTop (Stacks.AmpleTheory.powNonvanishingOpen X L n s) σ)) :=
          ((Stacks.SectionTensorFormula.tensorSection_whiskerRight (H.homologyπ p) τ
                (resTop (Stacks.AmpleTheory.powNonvanishingOpen X L n s) σ)).trans
            (congrArg (fun z => tensorSection (H.homology p) (tensorPowModule X L (m : ℤ)) z
              (resTop (Stacks.AmpleTheory.powNonvanishingOpen X L n s) σ)) hτ')).symm
      _ = Scheme.Modules.Hom.app (H.homologyπ p ▷ tensorPowModule X L (m : ℤ))
              (Stacks.AmpleTheory.powNonvanishingOpen X L n s)
              (resTop (Stacks.AmpleTheory.powNonvanishingOpen X L n s) ρ) :=
          congrArg (fun z => Scheme.Modules.Hom.app
            (H.homologyπ p ▷ tensorPowModule X L (m : ℤ))
            (Stacks.AmpleTheory.powNonvanishingOpen X L n s) z) heq.symm
      _ = 0 := hnat.symm.trans (by rw [hzero]; simp)

end Stacks.AmpleNonvanishingChart

end

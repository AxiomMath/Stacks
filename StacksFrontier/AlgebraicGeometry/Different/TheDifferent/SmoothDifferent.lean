module

public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.BaseChange
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.Basic
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.KaehlerComparison
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.SmoothBundle
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.SmoothFormula
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.SmoothTarget
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Syntomic
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothMorphisms.Basic

/-!
# The different of a quasi-finite morphism of smooth schemes

Let `S` be a locally Noetherian scheme, let `X` and `Y` be smooth of relative dimension `n` over
`S`, and let `f : Y ⟶ X` be a locally quasi-finite morphism over `S`.  This file states
[Stacks, Tag 0BWJ] for the different `𝔇_f = AlgebraicGeometry.Scheme.Hom.different f` of
[Stacks, Tag 0BW4] itself: the closed subscheme `R ⊆ Y` it cuts out is the locally principal
closed subscheme cut out by `∧ⁿ(df)`, and if `f` is étale at the associated points of `Y` then
`R` is an effective Cartier divisor with `f^*Ω^n_{X/S} ⊗ 𝒪_Y(R) ≅ Ω^n_{Y/S}`.

The closed subscheme `R` is `Stacks.Discriminant.differentIdealSheaf` of the relative dualizing
module `Stacks.Discriminant.relativeDualizingModuleData f` of [Stacks, Tag 0BVG] with its trace
element `Stacks.Discriminant.RelativeTraceSection.canonical` of [Stacks, Tag 0BVJ]: its ideal of
sections over every affine open is that of `f.different`
(`Stacks.Discriminant.different_sections_eq_kaehlerDifferent_ideal_of_smoothOfRelativeDimension`).

## Main results

* `Stacks.Discriminant.syntomic_of_smoothOfRelativeDimension_of_locallyQuasiFinite`: `f` is
  syntomic: flat by the first assertion of the tag, and a local complete intersection morphism
  by [Stacks, Tag 069M].
* `Stacks.Discriminant.differentIdealSheaf_eq_kaehlerDifferent_of_smoothOfRelativeDimension`:
  the different and the Kähler different of `f` are the same ideal sheaf ([Stacks, Tag 0BWG]).
* `Stacks.Discriminant.exists_chart_differentIdealSheaf_ideal_eq_span_det`,
  `Stacks.Discriminant.differentIdealSheaf_eq_zeroScheme_of_tensorFactorization` and
  `Stacks.Discriminant.isLocallyPrincipal_differentIdealSheaf_of_smoothOfRelativeDimension`:
  **[Stacks, Tag 0BWJ]**, `R` is the locally principal closed subscheme cut out by `∧ⁿ(df)`.
* `Stacks.Discriminant.isEffectiveCartierDivisor_differentIdealSheaf_of_smoothOfRelativeDimension`
  and `Stacks.Discriminant.nonempty_tensorIso_invertibleSheaf_differentIdealSheaf_of_etaleAt`:
  **[Stacks, Tag 0BWJ]**, the effective Cartier divisor and the bundle identity.

Flatness, the first assertion of the tag, is `Stacks.Discriminant.flat_of_locallyQuasiFinite`.

## Implementation notes

The proof is the source's: `f` is a local complete intersection morphism by
[Stacks, Tag 069M] and flat, hence syntomic, so [Stacks, Tag 0BWG]
(`Stacks.Discriminant.different_sections_eq_kaehlerDifferent_ideal`, stated for every relative
dualizing module datum) identifies the different with the Kähler different of
[Stacks, Tag 0BVW], for which the assertions are proved in `SmoothFormula.lean` and
`SmoothBundle.lean`.

The section `∧ⁿ(df)` of `(f^*Ω^n_{X/S})^{⊗ -1} ⊗ Ω^n_{Y/S}` is read through a tensor factorization
of the morphism `∧ⁿ(df) : f^*Ω^n_{X/S} ⟶ Ω^n_{Y/S}` (`Stacks.Discriminant.topFormsMap`): an
invertible module `ℳ` with a global section `σ` and an isomorphism `f^*Ω^n_{X/S} ⊗ ℳ ≅ Ω^n_{Y/S}`
carrying `x ⊗ σ` to `∧ⁿ(df)(x)`.  Such a factorization exists, `ℳ` is then
`(f^*Ω^n_{X/S})^{⊗ -1} ⊗ Ω^n_{Y/S}` with `σ = ∧ⁿ(df)`, and `R` is the zero scheme of `σ`.

Smoothness gives local Noetherianness of `X` and `Y` and local finite type of `f`, and the first
assertion of the tag gives flatness of `f`; the statements below supply these, which the
different needs in order to be defined, through `letI`.

## References

* [Stacks Project, Tag 0BWJ](https://stacks.math.columbia.edu/tag/0BWJ)
* [Stacks Project, Tag 0BW4](https://stacks.math.columbia.edu/tag/0BW4)
* [Stacks Project, Tag 0BWG](https://stacks.math.columbia.edu/tag/0BWG)
* [Stacks Project, Tag 069M](https://stacks.math.columbia.edu/tag/069M)
* [Stacks Project, Tag 069K](https://stacks.math.columbia.edu/tag/069K)
* [Stacks Project, Tag 0BVW](https://stacks.math.columbia.edu/tag/0BVW)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace (toTensorSheafSection)
open scoped TensorProduct

universe u

namespace Stacks.Discriminant

variable {S X Y : Scheme.{u}} (pX : X ⟶ S) (f : Y ⟶ X) (n : ℕ) [IsLocallyNoetherian S]
  [SmoothOfRelativeDimension n pX] [SmoothOfRelativeDimension n (f ≫ pX)] [LocallyQuasiFinite f]

include pX n in
/-- **A locally quasi-finite morphism of schemes smooth of the same relative dimension over a
locally Noetherian base is syntomic.**  It is flat by
`Stacks.Discriminant.flat_of_locallyQuasiFinite`, and a local complete intersection morphism by
[Stacks, Tag 069M], `Y ⟶ S` being smooth, hence syntomic and a local complete intersection
morphism, and `X ⟶ S` smooth; flat local complete intersection morphisms are syntomic
([Stacks, Tag 069K]). -/
theorem syntomic_of_smoothOfRelativeDimension_of_locallyQuasiFinite : Syntomic f := by
  have : Smooth pX := SmoothOfRelativeDimension.smooth n pX
  have : Smooth (f ≫ pX) := SmoothOfRelativeDimension.smooth n (f ≫ pX)
  exact syntomic_of_flat_of_isLocalCompleteIntersectionMorphism
    (flat_of_locallyQuasiFinite pX f n)
    (isLocalCompleteIntersectionMorphism_of_comp_of_smooth f pX
      (isLocalCompleteIntersectionMorphism_of_syntomic (syntomic_of_smooth (f ≫ pX))))

/-- **The different of `f` is its Kähler different, on affine opens.**  The ideal of sections of
the different `f.different` of [Stacks, Tag 0BW4] over every affine open of `Y` is the ideal of
the Kähler different there: [Stacks, Tag 0BWG], `f` being syntomic. -/
theorem different_sections_eq_kaehlerDifferent_ideal_of_smoothOfRelativeDimension
    (V : Y.affineOpens) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_smoothOfRelativeDimension pX f n
    letI : IsLocallyNoetherian X := isLocallyNoetherian_of_smoothOfRelativeDimension pX n
    letI : IsLocallyNoetherian Y := isLocallyNoetherian_of_smoothOfRelativeDimension (f ≫ pX) n
    letI : Flat f := flat_of_locallyQuasiFinite pX f n
    (show Ideal Γ(Y, V.1) from f.different.toSubmodule.obj (op V.1)) =
      (kaehlerDifferent f).ideal V := by
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_smoothOfRelativeDimension pX f n
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_smoothOfRelativeDimension pX n
  let : IsLocallyNoetherian Y := isLocallyNoetherian_of_smoothOfRelativeDimension (f ≫ pX) n
  let : Flat f := flat_of_locallyQuasiFinite pX f n
  exact different_sections_eq_kaehlerDifferent_ideal
    (syntomic_of_smoothOfRelativeDimension_of_locallyQuasiFinite pX f n)
    (relativeDualizingModuleData f) (RelativeTraceSection.canonical (relativeDualizingModuleData f))
    V

/-- **The closed subscheme cut out by the different of `f` is the one cut out by its Kähler
different.**  `R` is the ideal sheaf `differentIdealSheaf` of the relative dualizing module of
[Stacks, Tag 0BVG] and its trace element of [Stacks, Tag 0BVJ], whose ideals of sections are
those of `f.different`; by [Stacks, Tag 0BWG] it is the Kähler different of `f`. -/
theorem differentIdealSheaf_eq_kaehlerDifferent_of_smoothOfRelativeDimension :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_smoothOfRelativeDimension pX f n
    letI : IsLocallyNoetherian X := isLocallyNoetherian_of_smoothOfRelativeDimension pX n
    letI : IsLocallyNoetherian Y := isLocallyNoetherian_of_smoothOfRelativeDimension (f ≫ pX) n
    letI : Flat f := flat_of_locallyQuasiFinite pX f n
    differentIdealSheaf (relativeDualizingModuleData f)
        (RelativeTraceSection.canonical (relativeDualizingModuleData f)) =
      kaehlerDifferent f := by
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_smoothOfRelativeDimension pX f n
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_smoothOfRelativeDimension pX n
  let : IsLocallyNoetherian Y := isLocallyNoetherian_of_smoothOfRelativeDimension (f ≫ pX) n
  let : Flat f := flat_of_locallyQuasiFinite pX f n
  exact Scheme.IdealSheafData.ext (funext fun V =>
    (differentIdealSheaf_ideal _ _ V).trans
      (different_sections_eq_kaehlerDifferent_ideal_of_smoothOfRelativeDimension pX f n V))

/-- **[Stacks, Tag 0BWJ], the local equation of `R`.**  Let `X` and `Y` be smooth of relative
dimension `n` over a locally Noetherian base `S` and let `f : Y ⟶ X` be a locally quasi-finite
morphism over `S`.  Every point of `Y` has an affine chart `V = Spec B` over an affine chart
`U = Spec A` of `X` over an affine chart `W = Spec R` of `S`, on which `Ω[A⁄R]` and `Ω[B⁄R]` are
free of rank `n` and the ideal of the closed subscheme `R ⊆ Y` cut out by the different of `f` is
generated by `∧ⁿ(df)`, the determinant of the matrix of `B ⊗_A Ω[A⁄R] → Ω[B⁄R]` in those bases. -/
@[stacks 0BWJ "the closed subscheme `R` cut out by the different of `f` (Tag 0BW4) is cut out
locally by `∧ⁿ(df)`: on affine charts `V = Spec B` over `U = Spec A` over `W = Spec R` of the
base, with bases of rank `n` of `Ω_{A/R}` and `Ω_{B/R}`, its ideal is generated by the determinant
of `B ⊗_A Ω_{A/R} → Ω_{B/R}`"]
theorem exists_chart_differentIdealSheaf_ideal_eq_span_det (y : Y) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_smoothOfRelativeDimension pX f n
    letI : IsLocallyNoetherian X := isLocallyNoetherian_of_smoothOfRelativeDimension pX n
    letI : IsLocallyNoetherian Y := isLocallyNoetherian_of_smoothOfRelativeDimension (f ≫ pX) n
    letI : Flat f := flat_of_locallyQuasiFinite pX f n
    ∃ (W : S.Opens) (hW : IsAffineOpen W) (U : X.affineOpens) (V : Y.affineOpens)
      (hUW : U.1 ≤ pX ⁻¹ᵁ W) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (hVW : V.1 ≤ (f ≫ pX) ⁻¹ᵁ W),
      y ∈ V.1 ∧
      letI := Stacks.Smooth.algebraAppLE pX hUW
      letI := Stacks.Smooth.algebraAppLE f hVU
      letI := Stacks.Smooth.algebraAppLE (f ≫ pX) hVW
      letI := isScalarTower_appLE pX f hUW hVU hVW
      ∃ (bA : Module.Basis (Fin n) Γ(X, U.1) Ω[Γ(X, U.1)⁄Γ(S, W)])
        (bB : Module.Basis (Fin n) Γ(Y, V.1) Ω[Γ(Y, V.1)⁄Γ(S, W)]),
        (differentIdealSheaf (relativeDualizingModuleData f)
            (RelativeTraceSection.canonical (relativeDualizingModuleData f))).ideal V =
          Ideal.span {(LinearMap.toMatrix (bA.baseChange Γ(Y, V.1)) bB
            (KaehlerDifferential.mapBaseChange Γ(S, W) Γ(X, U.1) Γ(Y, V.1))).det} := by
  rw [differentIdealSheaf_eq_kaehlerDifferent_of_smoothOfRelativeDimension pX f n]
  exact exists_chart_kaehlerDifferent_ideal_eq_span_det pX f n y

/-- **[Stacks, Tag 0BWJ], `R` is cut out by the section `∧ⁿ(df)`.**  The morphism
`∧ⁿ(df) : f^*Ω^n_{X/S} ⟶ Ω^n_{Y/S}` of invertible modules is a section of
`(f^*Ω^n_{X/S})^{⊗ -1} ⊗ Ω^n_{Y/S}`: there is an invertible module `ℳ` with a global section `σ`
and an isomorphism `f^*Ω^n_{X/S} ⊗ ℳ ≅ Ω^n_{Y/S}` carrying `x ⊗ σ` to `∧ⁿ(df)(x)`, and for every
such factorization the zero scheme of `σ` is the closed subscheme `R ⊆ Y` cut out by the
different of `f`. -/
@[stacks 0BWJ "the closed subscheme `R` cut out by the different of `f` (Tag 0BW4) is the closed
subscheme cut out by `∧ⁿ(df) ∈ Γ(Y, (f^*Ω^n_{X/S})^{⊗ -1} ⊗ Ω^n_{Y/S})`: the section `σ` of an
invertible `ℳ` with `f^*Ω^n_{X/S} ⊗ ℳ ≅ Ω^n_{Y/S}` sending `x ⊗ σ` to `∧ⁿ(df)(x)`, which exists,
has zero scheme `R`"]
theorem differentIdealSheaf_eq_zeroScheme_of_tensorFactorization :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_smoothOfRelativeDimension pX f n
    letI : IsLocallyNoetherian X := isLocallyNoetherian_of_smoothOfRelativeDimension pX n
    letI : IsLocallyNoetherian Y := isLocallyNoetherian_of_smoothOfRelativeDimension (f ≫ pX) n
    letI : Flat f := flat_of_locallyQuasiFinite pX f n
    (∃ (M : Y.Modules) (σ : M.sections)
      (e : (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj
            ((Scheme.Modules.pullback f).obj
              (Scheme.Hom.relativeDifferentialForms pX (n : ℤ)))).obj M) ≅
        Scheme.Hom.relativeDifferentialForms (f ≫ pX) (n : ℤ)),
      AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M ∧
      ∀ (O : Y.Opens) (x : Γ((Scheme.Modules.pullback f).obj
          (Scheme.Hom.relativeDifferentialForms pX (n : ℤ)), O)),
        Scheme.Modules.Hom.app e.hom O
            (toTensorSheafSection Y.toRingedSpace ((Scheme.Modules.pullback f).obj
              (Scheme.Hom.relativeDifferentialForms pX (n : ℤ))) M (op O)
              (x ⊗ₜ[Y.presheaf.obj (op O)] σ.eval (op O))) =
          Scheme.Modules.Hom.app (topFormsMap pX f n) O x) ∧
    ∀ (M : Y.Modules)
      [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]
      (σ : M.sections)
      (e : (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj
            ((Scheme.Modules.pullback f).obj
              (Scheme.Hom.relativeDifferentialForms pX (n : ℤ)))).obj M) ≅
        Scheme.Hom.relativeDifferentialForms (f ≫ pX) (n : ℤ)),
      (∀ (O : Y.Opens) (x : Γ((Scheme.Modules.pullback f).obj
          (Scheme.Hom.relativeDifferentialForms pX (n : ℤ)), O)),
        Scheme.Modules.Hom.app e.hom O
            (toTensorSheafSection Y.toRingedSpace ((Scheme.Modules.pullback f).obj
              (Scheme.Hom.relativeDifferentialForms pX (n : ℤ))) M (op O)
              (x ⊗ₜ[Y.presheaf.obj (op O)] σ.eval (op O))) =
          Scheme.Modules.Hom.app (topFormsMap pX f n) O x) →
      zeroScheme Y M (σ.eval (op ⊤)) =
        differentIdealSheaf (relativeDualizingModuleData f)
          (RelativeTraceSection.canonical (relativeDualizingModuleData f)) := by
  rw [differentIdealSheaf_eq_kaehlerDifferent_of_smoothOfRelativeDimension pX f n]
  refine ⟨?_, fun M _ σ e he => zeroScheme_eq_kaehlerDifferent_of_tensorFactorization pX f n
    M σ e he⟩
  have : Stacks.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (_root_.structureSheafRing Y.toRingedSpace).property
      ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentialForms pX (n : ℤ))) :=
    isInvertible_pullback_relativeDifferentialForms pX f n
  have : Stacks.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (_root_.structureSheafRing Y.toRingedSpace).property
      (Scheme.Hom.relativeDifferentialForms (f ≫ pX) (n : ℤ)) :=
    isInvertible_relativeDifferentialForms (f ≫ pX) n
  obtain ⟨M, σ, e, hM, he⟩ :=
    Stacks.SheafOfModules.TensorFactorization.exists_tensorFactorization Y.toRingedSpace
      ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentialForms pX (n : ℤ)))
      (Scheme.Hom.relativeDifferentialForms (f ≫ pX) (n : ℤ)) (topFormsMap pX f n)
  exact ⟨M, σ, e, hM, fun O x => he (op O) x⟩

/-- **[Stacks, Tag 0BWJ], local principality.**  The closed subscheme `R ⊆ Y` cut out by the
different of `f` is locally principal: on the charts of
`Stacks.Discriminant.exists_chart_differentIdealSheaf_ideal_eq_span_det` it is cut out by the
single function `∧ⁿ(df)`. -/
@[stacks 0BWJ "the closed subscheme `R` cut out by the different of `f` (Tag 0BW4) is locally
principal"]
theorem isLocallyPrincipal_differentIdealSheaf_of_smoothOfRelativeDimension :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_smoothOfRelativeDimension pX f n
    letI : IsLocallyNoetherian X := isLocallyNoetherian_of_smoothOfRelativeDimension pX n
    letI : IsLocallyNoetherian Y := isLocallyNoetherian_of_smoothOfRelativeDimension (f ≫ pX) n
    letI : Flat f := flat_of_locallyQuasiFinite pX f n
    Stacks.Divisors.IsLocallyPrincipal
      (differentIdealSheaf (relativeDualizingModuleData f)
        (RelativeTraceSection.canonical (relativeDualizingModuleData f))) := by
  rw [differentIdealSheaf_eq_kaehlerDifferent_of_smoothOfRelativeDimension pX f n]
  exact isLocallyPrincipal_kaehlerDifferent pX f n

/-- **[Stacks, Tag 0BWJ], the effective Cartier divisor.**  If `f` is étale at the associated
points of `Y`, the closed subscheme `R ⊆ Y` cut out by the different of `f` is an effective
Cartier divisor: its local equation `∧ⁿ(df)` is a nonzerodivisor, because it does not vanish at
any associated point of `Y`. -/
@[stacks 0BWJ "if `f` is étale at the associated points of `Y` then the closed subscheme `R` cut
out by the different of `f` (Tag 0BW4) is an effective Cartier divisor"]
theorem isEffectiveCartierDivisor_differentIdealSheaf_of_smoothOfRelativeDimension
    (hét : ∀ y ∈ Stacks.Divisors.schemeAssociatedPoints Y, EtaleAt f y) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_smoothOfRelativeDimension pX f n
    letI : IsLocallyNoetherian X := isLocallyNoetherian_of_smoothOfRelativeDimension pX n
    letI : IsLocallyNoetherian Y := isLocallyNoetherian_of_smoothOfRelativeDimension (f ≫ pX) n
    letI : Flat f := flat_of_locallyQuasiFinite pX f n
    Stacks.Divisors.IsEffectiveCartierDivisor
      (differentIdealSheaf (relativeDualizingModuleData f)
        (RelativeTraceSection.canonical (relativeDualizingModuleData f))) := by
  rw [differentIdealSheaf_eq_kaehlerDifferent_of_smoothOfRelativeDimension pX f n]
  exact isEffectiveCartierDivisor_kaehlerDifferent_of_etaleAt pX f n hét

/-- **[Stacks, Tag 0BWJ], the bundle identity.**  If `f` is étale at the associated points of
`Y` then

`f^*Ω^n_{X/S} ⊗_{𝒪_Y} 𝒪_Y(R) ≅ Ω^n_{Y/S}`

as invertible sheaves on `Y`, where `R` is the closed subscheme cut out by the different of
`f`. -/
@[stacks 0BWJ "the bundle identity: if `f` is étale at the associated points of `Y` then
`f^*Ω^n_{X/S} ⊗_{𝒪_Y} 𝒪_Y(R) = Ω^n_{Y/S}` as invertible sheaves on `Y`, where `R` is the closed
subscheme cut out by the different of `f` (Tag 0BW4)"]
theorem nonempty_tensorIso_invertibleSheaf_differentIdealSheaf_of_etaleAt
    (hét : ∀ y ∈ Stacks.Divisors.schemeAssociatedPoints Y, EtaleAt f y) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_smoothOfRelativeDimension pX f n
    letI : IsLocallyNoetherian X := isLocallyNoetherian_of_smoothOfRelativeDimension pX n
    letI : IsLocallyNoetherian Y := isLocallyNoetherian_of_smoothOfRelativeDimension (f ≫ pX) n
    letI : Flat f := flat_of_locallyQuasiFinite pX f n
    Nonempty ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj
          ((Scheme.Modules.pullback f).obj
            (Scheme.Hom.relativeDifferentialForms pX (n : ℤ)))).obj
          (Stacks.Divisors.invertibleSheaf'
            (differentIdealSheaf (relativeDualizingModuleData f)
              (RelativeTraceSection.canonical (relativeDualizingModuleData f))))) ≅
      Scheme.Hom.relativeDifferentialForms (f ≫ pX) (n : ℤ)) := by
  rw [differentIdealSheaf_eq_kaehlerDifferent_of_smoothOfRelativeDimension pX f n]
  exact nonempty_tensorIso_invertibleSheaf_kaehlerDifferent_of_etaleAt pX f n hét

end Stacks.Discriminant

end

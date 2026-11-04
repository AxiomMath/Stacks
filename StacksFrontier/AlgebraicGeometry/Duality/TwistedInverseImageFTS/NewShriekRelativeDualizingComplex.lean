module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekCohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekTorAmplitude

/-!
# Lemmas 0BV5–0BV8 for `f_new^!`

Let `S` be a Noetherian scheme endowed with a dualizing complex `ω_S^•`. Then
[Stacks, Tag 0BV5], [Stacks, Tag 0BV6], [Stacks, Tag 0BV7] and [Stacks, Tag 0BV8] hold for any
morphism `f : X ⟶ Y` of schemes of finite type over `S`, separated or not, with `f^!` replaced
by `f_new^! = D_X ∘ Lf^* ∘ D_Y` ([Stacks, Tag 0BV9]). This file collects the four statements,
proved in

* `StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImageFTS/NewShriekFibreDimension.lean`
  (0BV5 and the first assertion of 0BV6),
* `StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImageFTS/NewShriekTorAmplitude.lean`
  (the second assertion of 0BV6),
* `StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImageFTS/NewShriekCohenMacaulay.lean`
  (0BV7 and 0BV8).

In each case the proof is the source's: the statement is local on `X`; on an affine open
`V ⊆ X` the restriction of `f_new^! 𝒪_Y` is `(V → Y)_new^! 𝒪_Y`, which is `(V → Y)^! 𝒪_Y` by
the closing remark of [Stacks, Tag 0AUE] since `V → Y` is separated
(`Stacks.Duality.NormalizedOnOpens.newShriekStructureSheafRestrictIso`); and for `V → Y`, a
morphism of `FTS_Y`, the lemmas of those files apply.

## Main results

* `Stacks.Duality.NormalizedOnOpens.newShriekStructureSheaf_spec` — **[Stacks, Tag 0BV9]**.

## Implementation notes

The situation is that of [Stacks, Tag 0AU4] in the form used throughout
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImageFTS/`: structure morphisms `p : X ⟶ S`
and `q : Y ⟶ S` of finite type over the Noetherian `S`, with `f ≫ q = p`; a dualizing complex
`ω_S^•` (`hωS`); the dualizing complexes `ω_X^•`, `ω_Y^•` normalized relative to `ω_S^•`
(`𝒦X`, `𝒦Y`, any choice, [Stacks, Tag 0AU5]); and the compactifications `c` computing the
upper shriek functors of the separated pieces (any choice). `f_new^! 𝒪_Y` is
`Stacks.Duality.NormalizedOnOpens.newShriekStructureSheaf`, at the standard model of the derived
category, where the derived internal hom and the derived pullback defining it live.

## References

* [Stacks Project, Tag 0BV9](https://stacks.math.columbia.edu/tag/0BV9)
* [Stacks Project, Tag 0BV5](https://stacks.math.columbia.edu/tag/0BV5)
* [Stacks Project, Tag 0BV6](https://stacks.math.columbia.edu/tag/0BV6)
* [Stacks Project, Tag 0BV7](https://stacks.math.columbia.edu/tag/0BV7)
* [Stacks Project, Tag 0BV8](https://stacks.math.columbia.edu/tag/0BV8)
* [Stacks Project, Tag 0AUE](https://stacks.math.columbia.edu/tag/0AUE)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Duality

namespace NormalizedOnOpens

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))
  {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S}
  {hp : IsFiniteTypeOverNoetherian p} {hq : IsFiniteTypeOverNoetherian q}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel.{u, u} S}
  (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
  (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS)
  (hpe : f ≫ q = p) (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)

include hpe hωS in
/-- **Stacks Project, Tag 0BV9 (Remark 48.21.7).** Let `S` be a Noetherian scheme endowed with a
dualizing complex `ω_S^•`, and let `f : X ⟶ Y` be a morphism of schemes of finite type over `S`,
not necessarily separated. With `ω_X^•`, `ω_Y^•` normalized relative to `ω_S^•` and
`f_new^! 𝒪_Y = D_X(Lf^* D_Y(𝒪_Y))`, Lemmas 0BV5, 0BV6, 0BV7 and 0BV8 hold with `f^!` replaced
by `f_new^!`:

1. (0BV5) for `x ∈ X` with image `y`, `H^i(f_new^! 𝒪_Y)_x ≠ 0 ⟹ -dim_x(X_y) ≤ i`;
2. (0BV6) if `f` is flat, then `H^i(f_new^! 𝒪_Y)_x ≠ 0 ⟹ -dim_x(X_y) ≤ i ≤ 0`, and if all
   fibres of `f` have dimension `≤ d`, then `f_new^! 𝒪_Y` has Tor amplitude in `[-d, 0]` as an
   object of `D(X, f^{-1}𝒪_Y)`;
3. (0BV7) if `f` is flat and quasi-finite, then `f_new^! 𝒪_Y = ω_{X/Y}[0]` for some coherent
   `𝒪_X`-module `ω_{X/Y}` flat over `Y`;
4. (0BV8) if `f` is Cohen–Macaulay, then `f_new^! 𝒪_Y = ω_{X/Y}[d]` for some coherent
   `𝒪_X`-module `ω_{X/Y}` flat over `Y`, where `d` is the locally constant relative dimension of
   `X` over `Y`: on the open and closed locus where the relative dimension is `d`, `f_new^! 𝒪_Y`
   is `ω_{X/Y}` placed in degree `-d`.

The local dimension `dim_x(X_y)` is named by a natural number `d`. -/
@[stacks 0BV9 "Lemmas 0BV5, 0BV6 (both assertions), 0BV7 and 0BV8 with f^! replaced by \
  f_new^! = D_X o Lf^* o D_Y, for every morphism of schemes of finite type over a Noetherian base \
  with a dualizing complex, separated or not"]
theorem newShriekStructureSheaf_spec :
    -- Lemma 0BV5
    (∀ (x : X) (d : ℕ), topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (d : WithBot ℕ∞) →
      ∀ i : ℤ, Nontrivial (((@DerivedCategory.homologyFunctor X.Modules _ _
        (PerfectApproximation.standardModel X) i).obj
          (newShriekStructureSheaf c f 𝒦X 𝒦Y)).presheaf.stalk x) → -(d : ℤ) ≤ i) ∧
    -- Lemma 0BV6
    (Flat f →
      (∀ (x : X) (d : ℕ),
        topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (d : WithBot ℕ∞) →
        ∀ i : ℤ, Nontrivial (((@DerivedCategory.homologyFunctor X.Modules _ _
          (PerfectApproximation.standardModel X) i).obj
            (newShriekStructureSheaf c f 𝒦X 𝒦Y)).presheaf.stalk x) → -(d : ℤ) ≤ i ∧ i ≤ 0) ∧
      ∀ d : ℕ, (∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞)) →
        letI := HasDerivedCategory.standard (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)
        letI := HasDerivedCategory.standard
          (StrictlyPerfect.OXMod.{u, u} (RingedSpace.inverseImage Y.toRingedSpace f.base))
        Stacks.Cohomology.TorAmplitude.HasTorAmplitude
          (RingedSpace.inverseImage Y.toRingedSpace f.base)
          ((Scheme.Hom.derivedScalarRestriction f).obj (newShriekStructureSheaf c f 𝒦X 𝒦Y))
          (-(d : ℤ)) 0) ∧
    -- Lemma 0BV7
    (Flat f → LocallyQuasiFinite f →
      letI := PerfectApproximation.standardModel X
      ∃ ω : X.Modules, ω.IsCoherent ∧ IsFlatOver f.toLRSHom.toShHom ω ∧
        Nonempty ((newShriekStructureSheaf c f 𝒦X 𝒦Y : DerivedCategory X.Modules) ≅
          (DerivedCategory.singleFunctor X.Modules 0).obj ω)) ∧
    -- Lemma 0BV8
    (∀ hCM : f.IsCohenMacaulay
        (isLocallyNoetherian_fiber_of_isFiniteTypeOverNoetherian (hp := hp) hpe),
      letI h := (isCohenMacaulay_iff_flat_and_fibers f
        (isLocallyNoetherian_fiber_of_isFiniteTypeOverNoetherian (hp := hp) hpe)).mp hCM
      letI : Flat f := h.1
      letI := locallyOfFinitePresentation_of_isFiniteTypeOverNoetherian (hp := hp) (hq := hq) hpe
      letI := PerfectApproximation.standardModel X
      ∃ ω : X.Modules, ω.IsCoherent ∧ IsFlatOver f.toLRSHom.toShHom ω ∧
        ∀ d : ℕ,
          letI := PerfectApproximation.standardModel (relativeDimensionOpen f h.2 d).toScheme
          Nonempty ((Scheme.Modules.restrictFunctor (relativeDimensionOpen f h.2 d).ι
              ).mapDerivedCategory.obj
                (newShriekStructureSheaf c f 𝒦X 𝒦Y : DerivedCategory X.Modules) ≅
            ((DerivedCategory.singleFunctor _ 0).obj
              ((Scheme.Modules.restrictFunctor (relativeDimensionOpen f h.2 d).ι).obj ω))⟦
                (d : ℤ)⟧)) :=
  ⟨fun x d hd i hi =>
      neg_fibreDim_le_of_nontrivial_stalk_homology_newShriek c 𝒦X 𝒦Y hpe hωS x d hd i hi,
    fun hf => by
      have := hf
      exact ⟨fun x d hd i hi =>
          fibreDim_bounds_of_nontrivial_stalk_homology_newShriek_of_flat c 𝒦X 𝒦Y hpe hωS
            x d hd i hi,
        fun d hd => hasTorAmplitude_derivedScalarRestriction_newShriek c 𝒦X 𝒦Y hpe hωS d hd⟩,
    fun hf hqf => by
      have := hf
      have := hqf
      exact exists_isCoherent_isFlatOver_iso_single_newShriek c 𝒦X 𝒦Y hpe hωS,
    fun hCM => exists_isCoherent_isFlatOver_iso_shift_newShriek c 𝒦X 𝒦Y hpe hωS hCM⟩

end NormalizedOnOpens

end Stacks.Duality

end

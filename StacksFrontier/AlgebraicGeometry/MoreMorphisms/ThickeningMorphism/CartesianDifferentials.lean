module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.AffineChart
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Filtration
public import StacksFrontier.RingTheory.Nilpotent.UnramifiedDescent

/-!
# Vanishing of the relative differentials across a cartesian morphism of thickenings

Let

```
X --f--→ S
|        |
i        j
↓        ↓
X' -f'-→ S'
```

be a cartesian square of schemes in which `j` is a *finite-order* thickening, so that `i` is
automatically its base change. Then `Ω_{X/S} = 0` if and only if `Ω_{X'/S'} = 0`.

The implication from `f'` to `f` is base change. In the other direction the argument is
affine-local and reduces, by `Stacks.Thickenings.PowerFiltration`, to the case where `j` is a
first-order thickening; there the chart of `f'` is a ring map `A' → B'` whose reduction modulo a
square-zero ideal `I ⊆ A'` is the chart of `f`, and
`Algebra.formallyUnramified_of_isNilpotent_quotient` concludes: the base change of Kähler
differentials identifies `Ω_{B/A}` with `Ω_{B'/A'}/I Ω_{B'/A'}`, so the vanishing of the former
forces the vanishing of the latter.

## Main results

* `Stacks.Thickenings.formallyUnramified_iff_of_isFiniteOrderThickening`: **Stacks 09ZW**,
  part (5).

## Implementation notes

The library has no quasi-coherent module of relative differentials of a morphism of schemes, and
the vanishing of `Ω_{X/S}` is expressed instead by Mathlib's
`AlgebraicGeometry.FormallyUnramified`, which on an affine chart is exactly the vanishing of the
Kähler differentials of the corresponding ring map. This is the same convention as in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/ThickeningMorphism/EtaleLocalProperties.lean`, where
the algebraic-space form of the clause (part (4) of Stacks 0BPJ) is recorded. Since `Ω_{X/S}`
restricts to the Kähler differentials of the chart on every affine chart square, that condition
*is* the vanishing of `Ω_{X/S}`.

No finiteness condition on `f` is imposed: unlike part (6) of the same tag, which is this clause
together with local finite type, the vanishing of the relative differentials is a condition on an
arbitrary morphism, and the nilpotence of the ideal — not Nakayama for a finite module — is what
makes the descent work.

The induction over the power filtration is carried out on the base-changed projections
`Stacks.Thickenings.PowerFiltration.totalProjection`, whose endpoints are identified with `f`
and `f'` by the canonical isomorphisms of the filtration, exactly as for the local finite type
clause in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/ThickeningMorphism/Cartesian.lean`.

## References

* [Stacks Project, Tag 00RV](https://stacks.math.columbia.edu/tag/00RV)
* [Stacks Project, Tag 09ZW](https://stacks.math.columbia.edu/tag/09ZW)
* [Stacks Project, Tag 0BPJ](https://stacks.math.columbia.edu/tag/0BPJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.Thickenings

universe u

/-- The vanishing of the relative differentials ascends across a cartesian square of first-order
thickenings. -/
private theorem formallyUnramified_of_firstOrder
    {X X' S S' : Scheme.{u}} (i : X ⟶ X') (j : S ⟶ S')
    (f : X ⟶ S) (f' : X' ⟶ S')
    (hi : IsFirstOrderThickening i)
    (hj : IsFirstOrderThickening j)
    (hcart : IsPullback i f f' j)
    (hf : FormallyUnramified f) : FormallyUnramified f' := by
  refine ⟨fun {U'} hU' {V'} hV' hV'U' ↦ ?_⟩
  let U : S.Opens := j ⁻¹ᵁ U'
  let V : X.Opens := i ⁻¹ᵁ V'
  have _ : IsClosedImmersion j := hj.1
  have _ : IsClosedImmersion i := hi.1
  have hU : IsAffineOpen U := hU'.preimage j
  have hV : IsAffineOpen V := hV'.preimage i
  have hsq : i ≫ f' = f ≫ j := hcart.toCommSq.w
  have hVU : V ≤ f ⁻¹ᵁ U := by
    intro x hx
    show f x ∈ j ⁻¹ᵁ U'
    show j (f x) ∈ U'
    have hx' : f' (i x) = j (f x) := by
      simpa using congrArg (fun g : X ⟶ S' => g x) hsq
    rw [← hx']
    exact hV'U' hx
  let C : FirstOrderThickeningChart :=
    { X := X, X' := X', S := S, S' := S', i := i, j := j, f := f, f' := f'
      i_firstOrder := hi, j_firstOrder := hj, cartesian := hcart
      U' := U', V' := V', U'_affine := hU', V'_affine := hV', mapsTo := hV'U' }
  let α : Γ(S', U') →+* Γ(S, U) := (j.app U').hom
  let β : Γ(X', V') →+* Γ(X, V) := (i.app V').hom
  let φ : Γ(S, U) →+* Γ(X, V) := (f.appLE U V hVU).hom
  have hφ : φ.FormallyUnramified := FormallyUnramified.formallyUnramified_appLE f hU hV hVU
  have hcat : j.app U' ≫ f.appLE U V hVU = f'.appLE U' V' hV'U' ≫ i.app V' := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE f j U' U V (by simp [U]) hVU,
      Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE i f' U' V' V hV'U' (by simp [V])]
    exact appLE_eq_of_hom_eq (f ≫ j) (i ≫ f') hsq.symm U' V _ _
  have hcomm : φ.comp α = β.comp C.ringMap :=
    RingHom.ext fun a ↦ congrArg (fun g : Γ(S', U') ⟶ Γ(X, V) => g a) hcat
  let eA : (Γ(S', U') ⧸ C.baseIdeal) ≃+* Γ(S, U) :=
    RingHom.quotientKerEquivOfSurjective C.base_app_surjective
  let eB : (Γ(X', V') ⧸ C.sourceIdeal) ≃+* Γ(X, V) :=
    (Ideal.quotEquivOfEq C.sourceIdeal_eq_ker).trans
      (RingHom.quotientKerEquivOfSurjective C.source_app_surjective)
  have hq : C.quotientRingMap.FormallyUnramified := by
    have hq' : C.quotientRingMap = eB.symm.toRingHom.comp (φ.comp eA.toRingHom) := by
      apply RingHom.ext
      intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      apply eB.injective
      have hcomm' := congrArg (fun g => g a) hcomm
      simp only [RingHom.comp_apply] at hcomm'
      have hqmk := congrArg
        (fun g : Γ(S', U') →+* (Γ(X', V') ⧸ C.sourceIdeal) => g a)
        C.quotientRingMap_comp_mk
      simp only [RingHom.comp_apply] at hqmk
      rw [hqmk]
      simp [C, β, α, eB, eA, Ideal.quotEquivOfEq_mk,
        RingHom.quotientKerEquivOfSurjective_apply_mk, hcomm']
    rw [hq']
    exact RingHom.FormallyUnramified.comp
      (RingHom.FormallyUnramified.comp
        (RingHom.FormallyUnramified.of_surjective eA.surjective) hφ)
      (RingHom.FormallyUnramified.of_surjective eB.symm.surjective)
  let _ : Algebra (Γ(S', U')) (Γ(X', V')) := C.ringMap.toAlgebra
  let qAlg : Algebra (Γ(S', U') ⧸ C.baseIdeal) (Γ(X', V') ⧸ C.sourceIdeal) :=
    C.quotientRingMap.toAlgebra
  have hAlg : qAlg = (Ideal.Quotient.algebraQuotientMapQuotient :
      Algebra (Γ(S', U') ⧸ C.baseIdeal) (Γ(X', V') ⧸ C.sourceIdeal)) := by
    apply Algebra.algebra_ext
    intro a
    show C.quotientRingMap a =
      (Ideal.quotientMap C.sourceIdeal
        (algebraMap (Γ(S', U')) (Γ(X', V'))) Ideal.le_comap_map) a
    simp [FirstOrderThickeningChart.quotientRingMap, RingHom.algebraMap_toAlgebra]
  have hfuQuot : @Algebra.FormallyUnramified
      (Γ(S', U') ⧸ C.baseIdeal) (Γ(X', V') ⧸ C.sourceIdeal) _ _
      (Ideal.Quotient.algebraQuotientMapQuotient) := by
    rw [← hAlg]
    exact hq
  exact RingHom.formallyUnramified_algebraMap.mpr
    (Algebra.formallyUnramified_of_isNilpotent_quotient (Γ(S', U')) C.baseIdeal (Γ(X', V'))
      ⟨2, C.baseIdeal_sq_eq_bot⟩ hfuQuot)

/-- The vanishing of the relative differentials is preserved along the power filtration of a
closed immersion. -/
private theorem formallyUnramified_totalProjection_steps
    {S S' X' : Scheme.{u}} (j : S ⟶ S') (f' : X' ⟶ S') (n : ℕ) :
    FormallyUnramified (PowerFiltration.totalProjection j f' 0) ↔
      FormallyUnramified (PowerFiltration.totalProjection j f' n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact ih.trans ⟨formallyUnramified_of_firstOrder
      (PowerFiltration.totalStep j f' n) (PowerFiltration.baseStep j n)
      (PowerFiltration.totalProjection j f' n)
      (PowerFiltration.totalProjection j f' (n + 1))
      (PowerFiltration.totalStep_firstOrder j f' n)
      (PowerFiltration.baseStep_firstOrder j n)
      (PowerFiltration.totalStep_isPullback j f' n),
      MorphismProperty.of_isPullback (PowerFiltration.totalStep_isPullback j f' n)⟩

/-- **Stacks 09ZW, part (5).** The relative differentials of `f` vanish exactly when the
relative differentials of `f'` vanish, for a cartesian morphism of thickenings whose base
thickening has finite order. -/
@[stacks 09ZW "vanishing_differentials"]
theorem formallyUnramified_iff_of_isFiniteOrderThickening
    {X X' S S' : Scheme.{u}} (i : X ⟶ X') (j : S ⟶ S')
    (f : X ⟶ S) (f' : X' ⟶ S')
    (hj : IsFiniteOrderThickening j)
    (hcart : IsPullback i f f' j) :
    FormallyUnramified f ↔ FormallyUnramified f' := by
  refine ⟨fun hf ↦ ?_, MorphismProperty.of_isPullback hcart⟩
  obtain ⟨n, hn⟩ := hj.2
  obtain ⟨e₀, _, he₀⟩ := PowerFiltration.totalLevel_zero_iso j f' i f hcart hj.1
  have _ := PowerFiltration.baseInitialMap_isIso j hj.1
  have : MorphismProperty.RespectsIso (@FormallyUnramified.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hproj0 : FormallyUnramified (PowerFiltration.totalProjection j f' 0) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso (@FormallyUnramified.{u}) e₀.hom, he₀]
    exact (MorphismProperty.cancel_right_of_respectsIso (@FormallyUnramified.{u}) f
      (asIso (PowerFiltration.baseInitialMap j)).hom).mpr hf
  have _ := PowerFiltration.totalInclusion_isIso j f' hn
  have _ := PowerFiltration.baseInclusion_isIso j hn
  rw [← MorphismProperty.cancel_left_of_respectsIso (@FormallyUnramified.{u})
    (asIso (PowerFiltration.totalInclusion j f' n)).hom f', asIso_hom, pullback.condition]
  exact (MorphismProperty.cancel_right_of_respectsIso (@FormallyUnramified.{u}) _
    (asIso (PowerFiltration.baseInclusion j n)).hom).mpr
    ((formallyUnramified_totalProjection_steps j f' n).mp hproj0)

end Stacks.Thickenings

end

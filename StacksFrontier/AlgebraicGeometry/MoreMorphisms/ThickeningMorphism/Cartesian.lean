module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.AffineChart
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Filtration
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Separated
public import StacksFrontier.RingTheory.Nilpotent.Descent

/-!
# Finiteness properties across a cartesian morphism of thickenings

Let

```
X --f--→ S
|        |
i        j
↓        ↓
X' -f'-→ S'
```

be a cartesian square in which `j` is a *finite-order* thickening, so that `i` is automatically
its base change and no separate hypothesis on `i` is needed. Then `f` is locally of finite
type, locally quasi-finite or proper exactly when `f'` is.

For local finite type the argument is affine-local and reduces, by
`Stacks.Thickenings.PowerFiltration`, to the case where `j` is a first-order thickening; there
the chart of `f'` is a ring map whose reduction modulo a square-zero ideal is of finite type,
and Stacks Tag 0G8U concludes. Local quasi-finiteness adds to that the fibre condition, which
is purely topological because `i` and `j` are homeomorphisms. Properness is the conjunction of
local finite type, separatedness and universal closedness, the last two of which hold for any
morphism of thickenings.

## Main results

* `Stacks.Thickenings.locallyOfFiniteType_iff_of_isFiniteOrderThickening`
* `Stacks.Thickenings.locallyQuasiFinite_iff_of_isFiniteOrderThickening`
* `Stacks.Thickenings.isProper_iff_of_isFiniteOrderThickening`

## Implementation notes

Following Stacks Tag 01TD, local quasi-finiteness is spelled as the conjunction of Mathlib's
`AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.LocallyQuasiFinite`, the latter
being the fibre-isolation condition alone.

The induction over the power filtration is carried out on the base-changed projections
`Stacks.Thickenings.PowerFiltration.totalProjection`, whose endpoints are identified with `f`
and `f'` by the canonical isomorphisms of the filtration.

## References

* [Stacks Project, Tag 09ZW](https://stacks.math.columbia.edu/tag/09ZW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.Thickenings

universe u

/-- Local finite type ascends across a cartesian square of first-order thickenings. -/
private theorem locallyOfFiniteType_of_firstOrder
    {X X' S S' : Scheme.{u}} (i : X ⟶ X') (j : S ⟶ S')
    (f : X ⟶ S) (f' : X' ⟶ S')
    (hi : IsFirstOrderThickening i)
    (hj : IsFirstOrderThickening j)
    (hcart : IsPullback i f f' j)
    (hf : LocallyOfFiniteType f) : LocallyOfFiniteType f' := by
  refine ⟨?_⟩
  intro U' hU' V' hV' hV'U'
  let U : S.Opens := j ⁻¹ᵁ U'
  let V : X.Opens := i ⁻¹ᵁ V'
  have _ : IsClosedImmersion j := hj.1
  have _ : IsClosedImmersion i := hi.1
  have hU : IsAffineOpen U := hU'.preimage j
  have hV : IsAffineOpen V := hV'.preimage i
  have hsq : i ≫ f' = f ≫ j := hcart.toCommSq.w
  have hVU : V ≤ f ⁻¹ᵁ U := by
    intro x hx
    change j (f x) ∈ U'
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
  have hφ : φ.FiniteType := LocallyOfFiniteType.finiteType_appLE f hU hV hVU
  have hcat : j.app U' ≫ f.appLE U V hVU = f'.appLE U' V' hV'U' ≫ i.app V' := by
    have hleft := Scheme.Hom.appLE_comp_appLE f j U' U V (by simp [U]) hVU
    have hright := Scheme.Hom.appLE_comp_appLE i f' U' V' V hV'U' (by simp [V])
    rw [Scheme.Hom.app_eq_appLE, hleft, Scheme.Hom.app_eq_appLE, hright]
    exact appLE_eq_of_hom_eq (f ≫ j) (i ≫ f') hsq.symm U' V _ _
  have hcomm : φ.comp α = β.comp C.ringMap :=
    RingHom.ext fun a => congrArg (fun g : Γ(S', U') ⟶ Γ(X, V) => g a) hcat
  let eA : (Γ(S', U') ⧸ C.baseIdeal) ≃+* Γ(S, U) :=
    RingHom.quotientKerEquivOfSurjective C.base_app_surjective
  let eB : (Γ(X', V') ⧸ C.sourceIdeal) ≃+* Γ(X, V) :=
    (Ideal.quotEquivOfEq C.sourceIdeal_eq_ker).trans
      (RingHom.quotientKerEquivOfSurjective C.source_app_surjective)
  have hq : C.quotientRingMap.FiniteType := by
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
    have hφA : (φ.comp eA.toRingHom).FiniteType :=
      RingHom.FiniteType.comp hφ (RingHom.FiniteType.of_surjective _ eA.surjective)
    rw [hq']
    exact RingHom.FiniteType.comp
      (RingHom.FiniteType.of_surjective _ eB.symm.surjective) hφA
  let _ : Algebra (Γ(S', U')) (Γ(X', V')) := C.ringMap.toAlgebra
  let qAlg : Algebra (Γ(S', U') ⧸ C.baseIdeal) (Γ(X', V') ⧸ C.sourceIdeal) :=
    C.quotientRingMap.toAlgebra
  have hAlg : qAlg = (Ideal.Quotient.algebraQuotientMapQuotient :
      Algebra (Γ(S', U') ⧸ C.baseIdeal) (Γ(X', V') ⧸ C.sourceIdeal)) := by
    apply Algebra.algebra_ext
    intro a
    change C.quotientRingMap a =
      (Ideal.quotientMap C.sourceIdeal
        (algebraMap (Γ(S', U')) (Γ(X', V'))) Ideal.le_comap_map) a
    simp [FirstOrderThickeningChart.quotientRingMap, RingHom.algebraMap_toAlgebra]
  have hftQuot : @Algebra.FiniteType
      (Γ(S', U') ⧸ C.baseIdeal) (Γ(X', V') ⧸ C.sourceIdeal) _ _
      (Ideal.Quotient.algebraQuotientMapQuotient) := by
    rw [← hAlg]
    exact hq
  exact RingHom.finiteType_algebraMap.mpr
    (finiteType_of_isNilpotent_quotient_finiteType (Γ(S', U')) C.baseIdeal (Γ(X', V'))
      ⟨2, C.baseIdeal_sq_eq_bot⟩ hftQuot)

/-- Local finite type is preserved along the power filtration of a closed immersion. -/
private theorem locallyOfFiniteType_totalProjection_steps
    {S S' X' : Scheme.{u}} (j : S ⟶ S') (f' : X' ⟶ S') (n : ℕ) :
    LocallyOfFiniteType (PowerFiltration.totalProjection j f' 0) ↔
      LocallyOfFiniteType (PowerFiltration.totalProjection j f' n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact ih.trans ⟨locallyOfFiniteType_of_firstOrder
      (PowerFiltration.totalStep j f' n) (PowerFiltration.baseStep j n)
      (PowerFiltration.totalProjection j f' n)
      (PowerFiltration.totalProjection j f' (n + 1))
      (PowerFiltration.totalStep_firstOrder j f' n)
      (PowerFiltration.baseStep_firstOrder j n)
      (PowerFiltration.totalStep_isPullback j f' n),
      fun hf' => MorphismProperty.of_isPullback
        (PowerFiltration.totalStep_isPullback j f' n) hf'⟩

/-- Local finite type ascends and descends across a cartesian morphism of thickenings when
the thickening of the base has finite order. -/
@[stacks 09ZW "locally_finite_type"]
theorem locallyOfFiniteType_iff_of_isFiniteOrderThickening
    {X X' S S' : Scheme.{u}} (i : X ⟶ X') (j : S ⟶ S')
    (f : X ⟶ S) (f' : X' ⟶ S')
    (hj : IsFiniteOrderThickening j)
    (hcart : IsPullback i f f' j) :
    LocallyOfFiniteType f ↔ LocallyOfFiniteType f' := by
  refine ⟨fun hf => ?_, fun hf' => MorphismProperty.of_isPullback hcart hf'⟩
  obtain ⟨n, hn⟩ := hj.2
  obtain ⟨e₀, _, he₀⟩ := PowerFiltration.totalLevel_zero_iso j f' i f hcart hj.1
  have _ := PowerFiltration.baseInitialMap_isIso j hj.1
  let lofP : MorphismProperty Scheme.{u} := @LocallyOfFiniteType
  have hproj0 : LocallyOfFiniteType (PowerFiltration.totalProjection j f' 0) := by
    refine (MorphismProperty.cancel_left_of_respectsIso lofP e₀.hom _).mp ?_
    rw [he₀]
    exact (MorphismProperty.cancel_right_of_respectsIso lofP f _).mpr hf
  have _ := PowerFiltration.totalInclusion_isIso j f' hn
  have _ := PowerFiltration.baseInclusion_isIso j hn
  refine (MorphismProperty.cancel_left_of_respectsIso lofP
    (PowerFiltration.totalInclusion j f' n) f').mp ?_
  rw [pullback.condition]
  exact (MorphismProperty.cancel_right_of_respectsIso lofP _ _).mpr
    ((locallyOfFiniteType_totalProjection_steps j f' n).mp hproj0)

/-- **Local quasi-finiteness is invariant under a cartesian morphism of thickenings.** In a
cartesian square whose two vertical maps are thickenings the vertical maps are homeomorphisms
carrying the fibres of `f` onto the fibres of `f'`, so once both horizontal maps are known to
be locally of finite type one of them has discrete fibres exactly when the other does. No
finiteness condition on the two thickenings is used. -/
theorem locallyQuasiFinite_iff_of_isThickening
    {X X' S S' : Scheme.{u}} {i : X ⟶ X'} {j : S ⟶ S'} {f : X ⟶ S} {f' : X' ⟶ S'}
    (hi : IsThickening i) (hj : IsThickening j) (sq : IsPullback i f f' j)
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] :
    LocallyQuasiFinite f ↔ LocallyQuasiFinite f' := by
  have _ : IsClosedImmersion i := hi.1
  have _ : IsClosedImmersion j := hj.1
  have hiHomeo : IsHomeomorph i := isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨i.isClosedEmbedding.isEmbedding, hi.2⟩
  have hjHomeo : IsHomeomorph j := isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨j.isClosedEmbedding.isEmbedding, hj.2⟩
  let ei : X ≃ₜ X' := hiHomeo.homeomorph i
  have hcomm (x : X) : f' (i x) = j (f x) := by
    simpa [Scheme.Hom.comp_apply] using congrArg (fun k : X ⟶ S' => k x) sq.w
  have hImage (s : S) : ei '' (f ⁻¹' {s}) = f' ⁻¹' {j s} := by
    ext x'; constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hcomm x).trans (congrArg j hx)
    · intro hx
      obtain ⟨x, rfl⟩ := hiHomeo.surjective x'
      exact ⟨x, hjHomeo.injective ((hcomm x).symm.trans hx), rfl⟩
  have hDiscreteIff (s : S) :
      _root_.IsDiscrete (f ⁻¹' {s}) ↔ _root_.IsDiscrete (f' ⁻¹' {j s}) := by
    refine ⟨fun hs => (hImage s) ▸ hs.image ei.isInducing, ?_⟩
    intro hs
    simpa [← hImage s, Set.image_image] using hs.image ei.symm.isInducing
  rw [locallyQuasiFinite_iff_isDiscrete_preimage_singleton,
    locallyQuasiFinite_iff_isDiscrete_preimage_singleton]
  constructor
  · intro h y
    obtain ⟨s, rfl⟩ := hjHomeo.surjective y
    exact (hDiscreteIff s).mp (h s)
  · exact fun h s => (hDiscreteIff s).mpr (h (j s))

/-- Local quasi-finiteness is invariant under a cartesian morphism of thickenings when the
thickening of the base has finite order. -/
@[stacks 09ZW "locally_quasi_finite"]
theorem locallyQuasiFinite_iff_of_isFiniteOrderThickening
    {X X' S S' : Scheme.{u}} (i : X ⟶ X') (j : S ⟶ S')
    (f : X ⟶ S) (f' : X' ⟶ S')
    (hi : IsThickening i)
    (hj : IsFiniteOrderThickening j)
    (sq : IsPullback i f f' j) :
    (LocallyOfFiniteType f ∧ LocallyQuasiFinite f) ↔
      (LocallyOfFiniteType f' ∧ LocallyQuasiFinite f') := by
  have hft : LocallyOfFiniteType f ↔ LocallyOfFiniteType f' :=
    locallyOfFiniteType_iff_of_isFiniteOrderThickening i j f f' hj sq
  have hqf (hf : LocallyOfFiniteType f) (hf' : LocallyOfFiniteType f') :
      LocallyQuasiFinite f ↔ LocallyQuasiFinite f' :=
    locallyQuasiFinite_iff_of_isThickening hi hj.isThickening sq
  exact ⟨fun h => ⟨hft.mp h.1, (hqf h.1 (hft.mp h.1)).mp h.2⟩,
    fun h => ⟨hft.mpr h.1, (hqf (hft.mpr h.1) h.1).mpr h.2⟩⟩

/-- Properness ascends and descends along a cartesian morphism of thickenings when the
thickening of the base has finite order. -/
@[stacks 09ZW "proper"]
theorem isProper_iff_of_isFiniteOrderThickening
    {X X' S S' : Scheme.{u}} (i : X ⟶ X') (j : S ⟶ S')
    (f : X ⟶ S) (f' : X' ⟶ S')
    (hi : IsThickening i)
    (hj : IsFiniteOrderThickening j)
    (hcart : IsPullback i f f' j) :
    IsProper f ↔ IsProper f' := by
  let φ : Arrow.mk i ⟶ Arrow.mk j := Arrow.homMk f f' hcart.w.symm
  rw [isProper_iff, isProper_iff,
    (show IsSeparated f ↔ IsSeparated f' from
      isSeparated_left_iff_right hi hj.isThickening φ),
    (show UniversallyClosed f ↔ UniversallyClosed f' from
      universallyClosed_left_iff_right φ hi hj.isThickening),
    locallyOfFiniteType_iff_of_isFiniteOrderThickening i j f f' hj hcart]

end Stacks.Thickenings

end

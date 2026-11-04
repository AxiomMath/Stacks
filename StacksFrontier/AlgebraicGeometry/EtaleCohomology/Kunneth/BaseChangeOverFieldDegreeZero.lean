module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.DegreeZeroBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.BaseChangeOverFieldFirstFailure
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleBaseChangeAbOfSets
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Base change over a field in degree zero

The proof of [Stacks, Tag 0F1I] needs the condition `BC(Z ⟶ Spec K̄, n, 0)` of
[Stacks, Tag 0F02] for the reduction `Z` of `X_{K̄}`, and the source obtains it from
[Stacks, Tag 0EYS]. Tag 0EYS is about the *underived* base change map `f⁻¹g_* ⟶ h_*e⁻¹`, while
`BC(·, n, 0)` is about degree zero of the *derived* one. This file supplies the passage between
the two and the corollary the assembly
`Stacks.EtaleCohomology.BaseChangeOverField.derivedBaseChangeHolds_of_reduction` asks for.

## Main results

* `Stacks.EtaleCohomology.baseChangeHolds_zero_of_isIso_smallEtaleBaseChangeAb` — if the
  underived base change map is invertible in every diagram of [Stacks, Tag 0F02] over `f`, then
  `BC(f, n, 0)` holds for every `n`.
* `Stacks.EtaleCohomology.baseChangeHolds_zero_of_flat_geometricallyReduced` — `BC(f, n, 0)` for
  `f` flat, locally of finite presentation and with geometrically reduced fibres, by
  [Stacks, Tag 0EYS].
* `Stacks.EtaleCohomology.baseChangeHolds_zero_of_isReduced` — `BC(f, n, 0)` for a reduced scheme
  `X` locally of finite presentation over an algebraically closed field: such an `X` is flat over
  the field, and geometrically reduced by [Stacks, Tag 020I]
  (`AlgebraicGeometry.geometricallyReduced_of_isReduced`, an algebraically closed field being
  perfect).
* `Stacks.EtaleCohomology.BaseChangeOverField.baseChangeHolds_zero_reduction` — the case of the
  assembly: for `X` locally of finite type over a field `K`, the reduction `Z` of `X_{K̄}`
  satisfies `BC(Z ⟶ Spec K̄, n, 0)`.
* `BaseChangeOverField.derivedBaseChangeHolds_of_reduction_of_locallyOfFiniteType` — the assembly
  of the proof of [Stacks, Tag 0F1I] with its hypothesis `hDegreeZero` discharged, for `X`
  locally of finite type over `K`.

## Implementation notes

Over a field flatness is automatic, so the corollaries over a field ask only for local finite
presentation (respectively local finite type) and reducedness.

## References

* [Stacks Project, Tag 0F1I](https://stacks.math.columbia.edu/tag/0F1I)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* [Stacks Project, Tag 0EYS](https://stacks.math.columbia.edu/tag/0EYS)
* [Stacks Project, Tag 020I](https://stacks.math.columbia.edu/tag/020I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- **`BC(f, n, 0)` from the underived base change map.** If in every diagram of
[Stacks, Tag 0F02] over `f : X ⟶ S`, with both squares cartesian and `g` quasi-compact and
quasi-separated, the underived base change map `(f')⁻¹g_* ⟶ h_*e⁻¹` is an isomorphism, then
`BC(f, n, 0)` holds for every `n`. -/
theorem baseChangeHolds_zero_of_isIso_smallEtaleBaseChangeAb {X S : Scheme.{u}} (f : X ⟶ S)
    (H : ∀ ⦃S' X' T Y : Scheme.{u}⦄ (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S'),
      IsPullback p f' f s → ∀ (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (sq : IsPullback h e f' g),
        IsIso (smallEtaleBaseChangeAb f' g h e sq.w))
    (n : ℤ) : BaseChangeHolds f n 0 := by
  intro S' X' T Y s p f' hp g h e sq _ _ F _ q hq
  obtain rfl : q = 0 := by omega
  have := H s p f' hp g h e sq
  exact (isIso_higherBaseChangeMapAb_zero_app_iff f' g h e sq.w F).2 inferInstance

/-- **`BC(f, n, 0)` for a flat morphism locally of finite presentation with geometrically reduced
fibres.** Every base change `f'` of `f` has the same three properties, so its underived base
change maps are invertible by [Stacks, Tag 0EYS]
(`Stacks.EtaleCohomology.isIso_smallEtaleBaseChangeAb_of_flat_geometricallyReduced`). -/
theorem baseChangeHolds_zero_of_flat_geometricallyReduced {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [GeometricallyReduced f] (n : ℤ) :
    BaseChangeHolds f n 0 := by
  refine baseChangeHolds_zero_of_isIso_smallEtaleBaseChangeAb f
    (fun S' X' T Y s p f' hp g h e sq ↦ ?_) n
  have : Flat f' := MorphismProperty.of_isPullback hp inferInstance
  have : LocallyOfFinitePresentation f' := MorphismProperty.of_isPullback hp inferInstance
  have : GeometricallyReduced f' := MorphismProperty.of_isPullback hp inferInstance
  exact isIso_smallEtaleBaseChangeAb_of_flat_geometricallyReduced f' h e g sq

/-- **`BC(f, n, 0)` for a reduced scheme locally of finite presentation over an algebraically
closed field.** Over a field `f` is flat, and a reduced scheme over a perfect field, such as an
algebraically closed one, is geometrically reduced over it ([Stacks, Tag 020I],
`AlgebraicGeometry.geometricallyReduced_of_isReduced`); so this is
`baseChangeHolds_zero_of_flat_geometricallyReduced`. -/
theorem baseChangeHolds_zero_of_isReduced (K : Type u) [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] [IsReduced X]
    (n : ℤ) : BaseChangeHolds f n 0 :=
  baseChangeHolds_zero_of_flat_geometricallyReduced f n

namespace BaseChangeOverField

variable (K : Type u) [Field K] {X : Scheme.{u}} (sX : X ⟶ Spec (.of K))

/-- **The degree-zero condition of the proof of [Stacks, Tag 0F1I].** For `X` locally of finite
type over a field `K`, the reduction `Z` of `X_{K̄} = Spec K̄ ×_K X` satisfies
`BC(Z ⟶ Spec K̄, n, 0)` for every `n`. The morphism `Z ⟶ Spec K̄` is locally of finite type,
hence locally of finite presentation over the noetherian scheme `Spec K̄`, and `Z` is reduced; so
this is `Stacks.EtaleCohomology.baseChangeHolds_zero_of_isReduced`. This is the hypothesis
`hDegreeZero` of `derivedBaseChangeHolds_of_reduction`. -/
theorem baseChangeHolds_zero_reduction [LocallyOfFiniteType sX] (n : ℤ) :
    BaseChangeHolds
      ((pullback (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))
        sX).nilradical.subschemeι ≫
          pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) sX)
      n 0 := by
  let φ := Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  have : IsReduced (pullback φ sX).nilradical.subscheme :=
    isReduced_nilradical_subscheme (pullback φ sX)
  have : LocallyOfFiniteType ((pullback φ sX).nilradical.subschemeι ≫ pullback.fst φ sX) :=
    inferInstance
  have : LocallyOfFinitePresentation
      ((pullback φ sX).nilradical.subschemeι ≫ pullback.fst φ sX) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  exact @baseChangeHolds_zero_of_isReduced (AlgebraicClosure K) _ _ _
    ((pullback φ sX).nilradical.subschemeι ≫ pullback.fst φ sX) _ _ n

/-- **[Stacks, Tag 0F1I] for a sheaf annihilated by `n`, for `X` locally of finite type, from the
steps not proved here.** This is `derivedBaseChangeHolds_of_reduction` with its hypothesis
`hDegreeZero` discharged by `baseChangeHolds_zero_reduction`. Let `K` be a field, `X` a scheme
locally of finite type over `K`, `n` an integer invertible in `K` and `Z` the reduction of
`X_{K̄}`. Granted [Stacks, Tag 0F09] (`hSmoothLimitBaseChange`) and [Stacks, Tag 0F08]
(`hFirstFailure`), if base change holds in the diagrams of [Stacks, Tag 0F1D] over `Z ⟶ Spec K̄`
(`hFunctionField`, the last paragraph of the source's proof), then derived base change for
sheaves annihilated by `n` holds over `X ⟶ Spec K`. -/
theorem derivedBaseChangeHolds_of_reduction_of_locallyOfFiniteType
    (hSmoothLimitBaseChange : SmoothLimitBaseChange.{u})
    (hFirstFailure : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ) (q : ℕ),
      BaseChangeHolds f n (q : ℤ) → ¬ BaseChangeHolds f n ((q : ℤ) + 1) →
        FirstFailureDiagram.NormalFailureDiagram f n (q + 1))
    [LocallyOfFiniteType sX] (n : ℤ) (hn : IsUnit (n : K))
    (hFunctionField : FunctionFieldBaseChange
      ((pullback (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))
        sX).nilradical.subschemeι ≫
          pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) sX)
      n) :
    DerivedBaseChangeHolds sX n :=
  derivedBaseChangeHolds_of_reduction hSmoothLimitBaseChange hFirstFailure K sX n hn
    (baseChangeHolds_zero_reduction K sX n) hFunctionField

end BaseChangeOverField

end Stacks.EtaleCohomology

end

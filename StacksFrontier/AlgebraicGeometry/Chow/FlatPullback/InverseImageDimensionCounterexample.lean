module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.MaximalDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.Base
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InverseImageDimension
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Facts
public import StacksCore.Tactic.StacksAttribute

/-!
# The first claim of Stacks 02R8 needs every component to meet the image

Stacks 02R8 reads: *Let `(S, δ)` be as in Situation 42.7.1. Let `X`, `Y` be locally of finite
type over `S`. Let `f : X → Y` be a morphism. Assume `f` is flat of relative dimension `r`. For
any closed subset `Z ⊂ Y` we have `dim_δ(f⁻¹(Z)) = dim_δ(Z) + r` provided `f⁻¹(Z)` is
nonempty. If `Z` is irreducible and `Z' ⊂ f⁻¹(Z)` is an irreducible component, then `Z'`
dominates `Z` and `dim_δ(Z') = dim_δ(Z) + r`.*

The proof says "it suffices to prove the final statement", which gives the first claim by
taking suprema over the irreducible components of `Z` — but only over those components that
`f⁻¹(Z)` lies over. A component of `Z` that the image of `f` misses contributes to `dim_δ(Z)`
and to nothing upstairs, so the first claim is false when only `f⁻¹(Z) ≠ ∅` is assumed. This
file proves that, and proves the formula that does hold under the source's hypotheses.

## The counterexample

Let `k` be a field and `S = Spec(k × k)`, a scheme with two points, neither a specialization of
the other. It is Noetherian and finite over `Spec k`, hence universally catenary (Stacks 02J9),
and since it has no non-trivial specialization every integer-valued function on it is a
dimension function; take `δ = 0` at the first point and `δ = 1` at the second. Let `Y = Z = S`
and let `f : X = Spec k → S` be the inclusion of the first point, induced by the first
projection `k × k → k`. That inclusion is an open immersion (the first projection is the
localization at the idempotent `(1, 0)`), hence flat of relative dimension `0`, and
`f⁻¹(Z) = X` is nonempty. But `dim_δ(f⁻¹(Z)) = 0` while `dim_δ(Z) + 0 = 1`.

## The formula that holds

Under the source's own hypotheses the computation of the proof gives
`dim_δ(f⁻¹(Z)) = sup { dim_δ(V) : V an irreducible component of Z meeting f(X) } + r`
(`Stacks.Chow.schemeDeltaDimension_pullback_snd_comp_eq_iSup_add`). When every irreducible
component of `Z` meets the image this is the source's formula, which is the base's
`Stacks.Chow.schemeDeltaDimension_pullback_snd_comp`.

## Main definitions

* `Stacks.Chow.twoPointBase` — the scheme `Spec(k × k)`.
* `Stacks.Chow.twoPointChowSituation` — `Spec(k × k)` with `δ = 0, 1` at its two points.
* `Stacks.Chow.firstPointInclusion` — the open immersion `Spec k → Spec(k × k)` of the first
  point.

## Main results

* `Stacks.Chow.schemeDeltaDimension_comp_eq_iSup_add` — for a flat morphism `p : P ⟶ Z` of
  relative dimension `r`, `dim_δ(P)` is `r` more than the supremum of `dim_δ(V)` over the
  irreducible components `V` of `Z` met by the image of `p`.
* `Stacks.Chow.schemeDeltaDimension_pullback_snd_comp_eq_iSup_add` — **Stacks 02R8**, the
  dimension formula for the inverse image at the source's hypotheses.
* `Stacks.Chow.schemeDeltaDimension_pullback_firstPointInclusion_ne` — the counterexample.
* `Stacks.Chow.not_forall_schemeDeltaDimension_pullback_snd_comp_of_nonempty` — **Stacks 02R8**:
  the first claim, with only `f⁻¹(Z) ≠ ∅` assumed, is false.

## References

* [Stacks Project, Tag 02R8](https://stacks.math.columbia.edu/tag/02R8)
* [Stacks Project, Tag 02J9](https://stacks.math.columbia.edu/tag/02J9)
* [Stacks Project, Tag 02I8](https://stacks.math.columbia.edu/tag/02I8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The formula at the source's hypotheses -/

/-- For a flat morphism `p : P ⟶ Z` of relative dimension `r` over the base, the delta-dimension
of `P` is `r` more than the supremum of the delta-dimensions of those irreducible components of
`Z` that the image of `p` meets. Every component of `P` lies over such a component, with
delta-dimension `r` more; and every such component has a component of `P` over it, because a
point of `P` over a point of the component generizes, by flatness, to one over its generic
point. -/
theorem schemeDeltaDimension_comp_eq_iSup_add (C : ChowSituation.{u}) {P Z : Scheme.{u}}
    (q : Z ⟶ C.S) [LocallyOfFiniteType q] (p : P ⟶ Z) [LocallyOfFiniteType p] [Flat p] (r : ℕ)
    (hrel : AlgebraicGeometry.RelativeDimension p r) :
    schemeDeltaDimension C (p ≫ q) =
      (⨆ V : {V : irreducibleComponents Z // ∃ x : P, p.base x ∈ (V.1 : Set Z)},
          (deltaDimension C q
            ⟨(V.1 : Set Z), V.1.2.1, isClosed_of_mem_irreducibleComponents (V.1 : Set Z) V.1.2⟩ :
            EInt)) + ((r : ℤ) : EInt) := by
  set α : irreducibleComponents P → EInt := fun W ↦
    (deltaDimension C (p ≫ q)
      ⟨(W : Set P), W.2.1, isClosed_of_mem_irreducibleComponents (W : Set P) W.2⟩ : EInt)
    with hαdef
  set β : {V : irreducibleComponents Z // ∃ x : P, p.base x ∈ (V.1 : Set Z)} → EInt := fun V ↦
    (deltaDimension C q
      ⟨(V.1 : Set Z), V.1.2.1, isClosed_of_mem_irreducibleComponents (V.1 : Set Z) V.1.2⟩ :
      EInt)
    with hβdef
  have hstep (W : irreducibleComponents P) (V : {V : irreducibleComponents Z //
      ∃ x : P, p.base x ∈ (V.1 : Set Z)})
      (hη : p.base W.2.1.genericPoint = genericPoints.ofComponent V.1) :
      α W = β V + ((r : ℤ) : EInt) := by
    rw [hαdef, hβdef, ← coe_add_coe_eq_coe_add]
    exact congrArg (fun z : ℤ ↦ (z : EInt))
      (deltaDimension_irreducibleComponent_eq_add C p q r hrel W V.1 hη)
  have hsource (W : irreducibleComponents P) :
      ∃ V, α W = β V + ((r : ℤ) : EInt) := by
    obtain ⟨V, hη⟩ := exists_irreducibleComponent_map_genericPoint p W
    refine ⟨⟨V, W.2.1.genericPoint, ?_⟩, hstep W _ hη⟩
    rw [hη]
    exact (genericPoints.isGenericPoint_ofComponent V).mem
  have htarget (V : {V : irreducibleComponents Z // ∃ x : P, p.base x ∈ (V.1 : Set Z)}) :
      ∃ W : irreducibleComponents P, α W = β V + ((r : ℤ) : EInt) := by
    obtain ⟨x, hxV⟩ := V.2
    have hηx : (genericPoints.ofComponent V.1 : Z) ⤳ p.base x :=
      (genericPoints.isGenericPoint_ofComponent V.1).specializes hxV
    obtain ⟨y, hyx, hpy⟩ := Flat.generalizingMap p hηx
    obtain ⟨T, hT, hyT⟩ := Set.mem_sUnion.mp
      (show y ∈ ⋃₀ irreducibleComponents P by rw [sUnion_irreducibleComponents]; simp)
    set W : irreducibleComponents P := ⟨T, hT⟩ with hWdef
    have hξy : W.2.1.genericPoint ⤳ y :=
      (W.2.1.isGenericPoint_genericPoint
        (isClosed_of_mem_irreducibleComponents (W : Set P) W.2)).specializes hyT
    obtain ⟨V', hV'⟩ := exists_irreducibleComponent_map_genericPoint p W
    have hmem : (genericPoints.ofComponent V.1 : Z) ∈ (V' : Set Z) := by
      have h := (hpy ▸ hξy.map p.continuous : p.base W.2.1.genericPoint ⤳
        (genericPoints.ofComponent V.1 : Z)).mem_closure
      rw [hV', (genericPoints.isGenericPoint_ofComponent V').def] at h
      exact h
    have hVV' : (V.1 : Set Z) ⊆ (V' : Set Z) := by
      rw [← (genericPoints.isGenericPoint_ofComponent V.1).def]
      exact closure_minimal (Set.singleton_subset_iff.mpr hmem)
        (isClosed_of_mem_irreducibleComponents (V' : Set Z) V'.2)
    have hVeq : V' = V.1 := Subtype.ext (Set.Subset.antisymm (V.1.2.2 V'.2.1 hVV') hVV')
    exact ⟨W, hstep W V (by rw [hV', hVeq])⟩
  rw [schemeDeltaDimension_eq_iSup]
  change (⨆ W, α W) = (⨆ V, β V) + ((r : ℤ) : EInt)
  rw [iSup_add_coe β (r : ℤ)]
  exact le_antisymm (iSup_mono' fun W ↦ (hsource W).imp fun _ h ↦ h.le)
    (iSup_mono' fun V ↦ (htarget V).imp fun _ h ↦ h.ge)

/-- **Stacks 02R8**, the dimension formula for the inverse image, at the source's hypotheses.
The source asserts `dim_δ(f⁻¹(Z)) = dim_δ(Z) + r` for a closed subscheme `i : Z ⟶ Y` and a flat
`f : X ⟶ Y` of relative dimension `r`, provided `f⁻¹(Z)` is nonempty; that is false
(`Stacks.Chow.not_forall_schemeDeltaDimension_pullback_snd_comp_of_nonempty`), because a component
of `Z` missed by the image of `f` counts in `dim_δ(Z)` and in nothing upstairs. What the source's
proof does establish, with no hypothesis beyond flatness and relative dimension `r`, is this:
`dim_δ(f⁻¹(Z))` is `r` more than the supremum of `dim_δ(V)` over the irreducible components `V`
of `Z` that `f⁻¹(Z)` lies over. When every irreducible component of `Z` has nonempty inverse
image that supremum is `dim_δ(Z)`, which is
`Stacks.Chow.schemeDeltaDimension_pullback_snd_comp`. -/
@[stacks 02R8 "corrected dimension formula: sup over the components of Z met by f⁻¹(Z)"]
theorem schemeDeltaDimension_pullback_snd_comp_eq_iSup_add (C : ChowSituation.{u})
    {X Y Z : Scheme.{u}} (g : Y ⟶ C.S) [LocallyOfFiniteType g] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Flat f] (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r)
    (i : Z ⟶ Y) [IsClosedImmersion i] :
    schemeDeltaDimension C (pullback.snd f i ≫ i ≫ g) =
      (⨆ V : {V : irreducibleComponents Z //
          ∃ x : (pullback f i : Scheme.{u}), (pullback.snd f i).base x ∈ (V.1 : Set Z)},
          (deltaDimension C (i ≫ g)
            ⟨(V.1 : Set Z), V.1.2.1, isClosed_of_mem_irreducibleComponents (V.1 : Set Z) V.1.2⟩ :
            EInt)) + ((r : ℤ) : EInt) :=
  have : Flat (pullback.snd f i) :=
    Flat.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f i) inferInstance
  schemeDeltaDimension_comp_eq_iSup_add C (i ≫ g) (pullback.snd f i) r
    (relativeDimension_pullback_snd f i r hf)

/-! ### A base with two points -/

variable (k : Type u) [Field k]

/-- The scheme `Spec(k × k)`: two points, neither a specialization of the other. -/
abbrev twoPointBase : Scheme.{u} := Spec (.of (k × k))

/-- Every specialization on `Spec(k × k)` is trivial: every prime ideal of `k × k` is maximal. -/
theorem eq_of_specializes_twoPointBase {x y : twoPointBase k} (h : x ⤳ y) : x = y := by
  have h' : (x : PrimeSpectrum (k × k)) ⤳ (y : PrimeSpectrum (k × k)) := h
  have hle : (x : PrimeSpectrum (k × k)).asIdeal ≤ (y : PrimeSpectrum (k × k)).asIdeal :=
    (PrimeSpectrum.le_iff_specializes _ _).mpr h'
  have : (x : PrimeSpectrum (k × k)).asIdeal.IsPrime := PrimeSpectrum.isPrime _
  have hmax : (x : PrimeSpectrum (k × k)).asIdeal.IsMaximal := Ideal.isMaximal_of_isPrime _
  exact PrimeSpectrum.ext (hmax.eq_of_le (PrimeSpectrum.isPrime (y : PrimeSpectrum (k × k))).ne_top
    hle)

open Classical in
/-- The dimension function on `Spec(k × k)` that is `1` at the prime containing `(1, 0)` and `0`
at the other one. Both conditions on a dimension function concern non-trivial specializations,
and `Spec(k × k)` has none. -/
def twoPointDimensionFunction : DimensionFunction (twoPointBase k) where
  toFun x := if ((1, 0) : k × k) ∈ (x : PrimeSpectrum (k × k)).asIdeal then 1 else 0
  strictAnti_specializes := fun {_ _} h hne => absurd (eq_of_specializes_twoPointBase k h) hne
  step_immediate := fun {_ _} h => absurd (eq_of_specializes_twoPointBase k h.1) h.2.1

/-- `Spec(k × k)` is universally catenary: it is finite over `Spec k`, which is universally
catenary, and universal catenarity passes to schemes locally of finite type (Stacks 02J9). -/
theorem isUniversallyCatenary_twoPointBase : Scheme.IsUniversallyCatenary (twoPointBase k) := by
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k (k × k)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    change (algebraMap k (k × k)).FiniteType
    rw [RingHom.finiteType_algebraMap]
    infer_instance
  exact Scheme.isUniversallyCatenary_of_locallyOfFiniteType
    (Spec.map (CommRingCat.ofHom (algebraMap k (k × k))))
    (Scheme.isUniversallyCatenary_spec_of_field k)

/-- The base situation `(Spec(k × k), δ)` with `δ = 0` and `δ = 1` at the two points. -/
abbrev twoPointChowSituation : ChowSituation.{u} where
  S := twoPointBase k
  isUniversallyCatenary := isUniversallyCatenary_twoPointBase k
  dimensionFunction := twoPointDimensionFunction k

/-- The inclusion `Spec k → Spec(k × k)` of the first point, induced by the first projection. -/
def firstPointInclusion : Spec (.of k) ⟶ twoPointBase k :=
  Spec.map (CommRingCat.ofHom (RingHom.fst k k))

/-- The first projection `k × k → k` is the localization at the idempotent `(1, 0)`, so the
inclusion of the first point is an open immersion. -/
instance : IsOpenImmersion (firstPointInclusion k) := by
  let _ : Algebra (k × k) k := (RingHom.fst k k).toAlgebra
  have : IsLocalization.Away ((1, 0) : k × k) k := by
    refine IsLocalization.away_of_isIdempotentElem (by ext <;> simp) ?_ ?_
    · ext ⟨a, b⟩
      simp only [RingHom.mem_ker, Ideal.mem_span_singleton]
      change a = 0 ↔ _
      constructor
      · rintro rfl
        exact ⟨(0, b), by ext <;> simp⟩
      · rintro ⟨c, hc⟩
        simpa using congrArg Prod.fst hc
    · exact fun a => ⟨(a, 0), rfl⟩
  exact IsOpenImmersion.of_isLocalization ((1, 0) : k × k)

/-- The first projection `k × k → k` is surjective, so the inclusion of the first point is also a
closed immersion. -/
instance : IsClosedImmersion (firstPointInclusion k) :=
  IsClosedImmersion.spec_of_surjective _ fun a => ⟨(a, 0), by simp⟩

/-- The inclusion of the first point is flat of relative dimension `0`: it is étale. -/
theorem relativeDimension_firstPointInclusion :
    AlgebraicGeometry.RelativeDimension (firstPointInclusion k) 0 :=
  relativeDimension_zero_of_etale _

/-- The image of the inclusion of the first point is the point where `δ` vanishes. -/
theorem twoPointDimensionFunction_firstPointInclusion (x : Spec (.of k)) :
    twoPointDimensionFunction k ((firstPointInclusion k).base x) = 0 := by
  have hx : ((1, 0) : k × k) ∉ (((firstPointInclusion k).base x : twoPointBase k) :
      PrimeSpectrum (k × k)).asIdeal := by
    change (RingHom.fst k k) (1, 0) ∉ (x : PrimeSpectrum k).asIdeal
    simpa using x.isPrime.ne_top ∘ (Ideal.eq_top_iff_one _).mpr
  simp [twoPointDimensionFunction, hx]

/-- The second point of `Spec(k × k)`, the kernel of the second projection. -/
def secondPoint : twoPointBase k :=
  (⟨RingHom.ker (RingHom.snd k k), RingHom.ker_isPrime _⟩ : PrimeSpectrum (k × k))

/-- The dimension function is `1` at the second point. -/
theorem twoPointDimensionFunction_secondPoint :
    twoPointDimensionFunction k (secondPoint k) = 1 := by
  have hx : ((1, 0) : k × k) ∈ ((secondPoint k : twoPointBase k) :
      PrimeSpectrum (k × k)).asIdeal := by
    change (RingHom.snd k k) (1, 0) = 0
    simp
  simp [twoPointDimensionFunction, hx]

/-- **The counterexample to the first claim of Stacks 02R8.** Over the base
`(Spec(k × k), δ)` with `δ = 0, 1` at the two points, take `Y = Z = Spec(k × k)` and the open
immersion `f : Spec k → Spec(k × k)` of the point where `δ = 0`. It is flat of relative
dimension `0`, and the inverse image `f⁻¹(Z) = Spec k` is nonempty, but
`dim_δ(f⁻¹(Z)) ≤ 0 < 1 ≤ dim_δ(Z) + 0`. -/
theorem schemeDeltaDimension_pullback_firstPointInclusion_ne :
    schemeDeltaDimension (twoPointChowSituation k)
        (pullback.snd (firstPointInclusion k) (𝟙 (twoPointBase k)) ≫ 𝟙 (twoPointBase k) ≫
          𝟙 (twoPointChowSituation k).S) ≠
      schemeDeltaDimension (twoPointChowSituation k)
          (𝟙 (twoPointBase k) ≫ 𝟙 (twoPointChowSituation k).S) + ((0 : ℤ) : EInt) := by
  set C := twoPointChowSituation k
  have hle : schemeDeltaDimension C
      (pullback.snd (firstPointInclusion k) (𝟙 (twoPointBase k)) ≫ 𝟙 (twoPointBase k) ≫
        𝟙 C.S) ≤ ((0 : ℤ) : EInt) := by
    refine schemeDeltaDimension_le_of_forall_relativeDimension_le C _ _ fun w => ?_
    rw [Category.comp_id, relativeDimension_id]
    have hw : (pullback.snd (firstPointInclusion k) (𝟙 (twoPointBase k))).base w =
        (firstPointInclusion k).base
          ((pullback.fst (firstPointInclusion k) (𝟙 (twoPointBase k))).base w) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Category.comp_id]
    rw [hw]
    exact (twoPointDimensionFunction_firstPointInclusion k _).le
  have hge : ((1 : ℤ) : EInt) ≤
      schemeDeltaDimension C (𝟙 (twoPointBase k) ≫ 𝟙 C.S) := by
    set V : irreducibleComponents (twoPointBase k) :=
      ⟨irreducibleComponent (secondPoint k), irreducibleComponent_mem_irreducibleComponents _⟩
    rw [schemeDeltaDimension_eq_iSup]
    refine le_trans ?_ (le_iSup _ V)
    refine WithBotTop.coe_le_coe.mpr ?_
    have hξ : V.2.1.genericPoint = secondPoint k :=
      eq_of_specializes_twoPointBase k ((V.2.1.isGenericPoint_genericPoint
        (isClosed_of_mem_irreducibleComponents _ V.2)).specializes
          mem_irreducibleComponent)
    change (1 : ℤ) ≤ relativeDimension C.dimensionFunction _ V.2.1.genericPoint
    rw [Category.comp_id, relativeDimension_id, hξ]
    exact (twoPointDimensionFunction_secondPoint k).ge
  intro h
  have h0 : ((0 : ℤ) : EInt) = 0 := rfl
  rw [h, h0, add_zero] at hle
  exact absurd (WithBotTop.coe_le_coe.mp (hge.trans (h0 ▸ hle))) (by norm_num)

/-- **Stacks 02R8**: the first claim, `dim_δ(f⁻¹(Z)) = dim_δ(Z) + r` for a closed subscheme
`Z ⊂ Y` provided only that `f⁻¹(Z)` is nonempty, is false. The counterexample is
`Stacks.Chow.schemeDeltaDimension_pullback_firstPointInclusion_ne`; the corrected formula is
`Stacks.Chow.schemeDeltaDimension_pullback_snd_comp_eq_iSup_add`, and under the additional
hypothesis that every irreducible component of `Z` has nonempty inverse image the source's
formula holds, `Stacks.Chow.schemeDeltaDimension_pullback_snd_comp`. -/
@[stacks 02R8 "the first claim is false as stated: f⁻¹(Z) nonempty does not suffice"]
theorem not_forall_schemeDeltaDimension_pullback_snd_comp_of_nonempty :
    ¬ ∀ (C : ChowSituation.{u}) {X Y Z : Scheme.{u}} (g : Y ⟶ C.S) [LocallyOfFiniteType g]
      (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f] (r : ℕ)
      (_ : AlgebraicGeometry.RelativeDimension f r) (i : Z ⟶ Y) [IsClosedImmersion i],
      Nonempty (pullback f i : Scheme.{u}) →
        schemeDeltaDimension C (pullback.snd f i ≫ i ≫ g) =
          schemeDeltaDimension C (i ≫ g) + ((r : ℤ) : EInt) := by
  intro h
  let k : Type u := ULift.{u} ℚ
  obtain ⟨x⟩ : Nonempty (Spec (.of k)) := inferInstance
  exact schemeDeltaDimension_pullback_firstPointInclusion_ne k
    (h (twoPointChowSituation k) (𝟙 (twoPointBase k)) (firstPointInclusion k) 0
      (relativeDimension_firstPointInclusion k) (𝟙 (twoPointBase k))
      ⟨(pullback.lift (𝟙 _) (firstPointInclusion k) (by simp)).base x⟩)

end Stacks.Chow

end

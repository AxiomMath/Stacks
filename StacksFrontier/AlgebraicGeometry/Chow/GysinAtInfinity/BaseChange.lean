module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.ProperModification
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.BaseChangeIsoGysinSystem
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FamilyFibreDifferenceExistence
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ExteriorProductCommuting

/-!
# The class at infinity commutes with base change (Stacks 0GUH)

Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over `S`, let
`b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, and let `C ∈ A⁰(W_∞ ⟶ X)` be the class
of Stacks 0F9J. For `q : X' ⟶ X` locally of finite type let
`b' : W' = W ×_{𝐏¹_X} 𝐏¹_{X'} ⟶ 𝐏¹_{X'}` be the base change of `b`, with fibre at infinity
`W'_∞ = W_∞ ×_X X'`. Stacks 0GUH asserts that the class `C' ∈ A⁰(W'_∞ ⟶ X')` constructed as in
Stacks 0F9J using `b'` is the restriction `res(C)` of Remark 0F9Z.

The proof is the one of the source. On a test scheme `g : T ⟶ X'` the comparison
`W' ×_{X'} T ≅ W ×_X T` identifies the opens over the affine charts, so it carries a lift
`β' ∈ A_{k+1}(W' ×_{X'} T)` of `α ∈ A_k(T)` to a lift of `α` on `W ×_X T` (flat pullback commutes
with pushforward along isomorphisms), and it carries the Gysin map of the divisor at infinity of
`W' ×_{X'} T` to that of `W ×_X T` (Stacks 02TA for an isomorphism). Hence
`C' ∩ α = (i'_∞)^* β'` and `C ∩ α = i_∞^* β` agree under `W'_∞ ×_{X'} T ≅ W_∞ ×_X T`, which is
the cap formula `res(C) ∩ α = C ∩ α` of the restriction.

## Main definitions

* `Stacks.Chow.GysinAtInfinity.baseChangedModification` — the base change
  `b' : W ×_{𝐏¹_X} 𝐏¹_{X'} ⟶ 𝐏¹_{X'}` of `b`.
* `Stacks.Chow.GysinAtInfinity.baseChangedInfinityIso` — the identification
  `W_∞ ×_X X' ≅ W'_∞` over `X'`.

## Main results

* `Stacks.Chow.GysinAtInfinity.isIso_baseChangedModification_chart` — `b'` is an isomorphism over
  `𝐀¹_{X'}` (it is proper by `isProper_baseChangedModification`).
* `Stacks.Chow.GysinAtInfinity.baseChangeTestInfinityMap_cap` — `C' ∩ α = C ∩ α` on every test
  scheme, under `W'_∞ ×_{X'} T ≅ W_∞ ×_X T`.
* `Stacks.Chow.GysinAtInfinity.gysinAtInfinityClass_baseChange` — **Stacks 0GUH**: `C' = res(C)`
  in `A⁰(W'_∞ ⟶ X')`.

## Implementation notes

The restriction `Stacks.Chow.bivariantRestrictionOfInvertible` of Remark 0F9Z is a class for the
chosen fibre product `W_∞ ×_X X' ⟶ X'`, while `C'` is a class for `W'_∞ ⟶ X'`; the source
identifies the two silently, and here the restriction is carried along
`baseChangedInfinityIso` by `Stacks.Chow.bivariantTransport`.

## References

* [Stacks Project, Tag 0GUH](https://stacks.math.columbia.edu/tag/0GUH)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

namespace GysinAtInfinity

/-! ### Base change of a pullback square to a test scheme -/

section TestLift

variable {P P' Y Y' T : Scheme.{u}} {a : P' ⟶ P} {π' : P' ⟶ Y'} {π : P ⟶ Y} {q : Y' ⟶ Y}

/-- For a cartesian square `P' = P ×_Y Y'` and a test scheme `g : T ⟶ Y'`, the comparison
morphism `P' ×_{Y'} T ⟶ P ×_Y T`. -/
def pullbackLiftOfIsPullback (h : IsPullback a π' π q) (g : T ⟶ Y') :
    pullback π' g ⟶ pullback π (g ≫ q) :=
  pullback.lift (pullback.fst π' g ≫ a) (pullback.snd π' g)
    (by rw [Category.assoc, h.w, ← Category.assoc, pullback.condition, Category.assoc])

/-- The comparison `P' ×_{Y'} T ⟶ P ×_Y T` followed by the first projection to `P` is the first
projection to `P'` followed by `P' ⟶ P`. -/
@[reassoc (attr := simp)]
theorem pullbackLiftOfIsPullback_fst (h : IsPullback a π' π q) (g : T ⟶ Y') :
    pullbackLiftOfIsPullback h g ≫ pullback.fst π (g ≫ q) = pullback.fst π' g ≫ a :=
  pullback.lift_fst _ _ _

/-- The comparison `P' ×_{Y'} T ⟶ P ×_Y T` lies over `T`. -/
@[reassoc (attr := simp)]
theorem pullbackLiftOfIsPullback_snd (h : IsPullback a π' π q) (g : T ⟶ Y') :
    pullbackLiftOfIsPullback h g ≫ pullback.snd π (g ≫ q) = pullback.snd π' g :=
  pullback.lift_snd _ _ _

/-- The comparison `P' ×_{Y'} T ⟶ P ×_Y T` is the base change of the identity of `T`. -/
theorem isPullback_pullbackLiftOfIsPullback (h : IsPullback a π' π q) (g : T ⟶ Y') :
    IsPullback (pullbackLiftOfIsPullback h g) (pullback.snd π' g) (pullback.snd π (g ≫ q))
      (𝟙 T) := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback π (g ≫ q))
  rw [pullbackLiftOfIsPullback_fst, Category.id_comp]
  exact (IsPullback.of_hasPullback π' g).paste_horiz h

/-- The comparison `P' ×_{Y'} T ⟶ P ×_Y T` is an isomorphism. -/
instance isIso_pullbackLiftOfIsPullback (h : IsPullback a π' π q) (g : T ⟶ Y') :
    IsIso (pullbackLiftOfIsPullback h g) :=
  (isPullback_pullbackLiftOfIsPullback h g).isIso_fst_of_isIso

end TestLift

/-! ### The base change of a modification -/

section Geometry

variable {X X' W S : Scheme.{u}} (f : X ⟶ S) (b : W ⟶ projectiveLineProduct f) (q : X' ⟶ X)

/-- The infinity section of `𝐏¹_{X'}` is the base change of that of `𝐏¹_X`. -/
theorem isPullback_infinitySection_familyBaseChange :
    IsPullback (infinitySection (q ≫ f)) q (familyBaseChange f q) (infinitySection f) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst (q ≫ f) (relativeProjectiveLine S ↘ S))
    (h₂₂ := pullback.fst f (relativeProjectiveLine S ↘ S)) (v₁₃ := q) ?_ ?_
    (isPullback_familyBaseChange f q)
  · rw [infinitySection_comp_fst, infinitySection_comp_fst]
    exact IsPullback.id_horiz q
  · exact constantSection_comp_familyBaseChange f q integralInfinitySection

/-- The base change `b' : W ×_{𝐏¹_X} 𝐏¹_{X'} ⟶ 𝐏¹_{X'}` of `b` along `𝐏¹_{X'} ⟶ 𝐏¹_X`. -/
abbrev baseChangedModification :
    pullback b (familyBaseChange f q) ⟶ projectiveLineProduct (q ≫ f) :=
  pullback.snd b (familyBaseChange f q)

/-- The base change `b'` of a proper morphism `b` is proper. -/
instance isProper_baseChangedModification [IsProper b] :
    IsProper (baseChangedModification f b q) := by
  unfold baseChangedModification
  infer_instance

/-- `W' = W ×_{𝐏¹_X} 𝐏¹_{X'}` is the base change `W ×_X X'`. -/
theorem isPullback_baseChangedModification :
    IsPullback (pullback.fst b (familyBaseChange f q))
      (modificationProjection (q ≫ f) (baseChangedModification f b q))
      (modificationProjection f b) q :=
  (IsPullback.of_hasPullback b (familyBaseChange f q)).paste_vert
    (isPullback_familyBaseChange f q).flip

/-- The projection of `W_∞` to `X` is the second projection of `W ×_{𝐏¹_X} X`. -/
theorem modificationProjectionAtInfinity_eq_snd :
    modificationProjectionAtInfinity f b = pullback.snd b (infinitySection f) := by
  rw [modificationProjectionAtInfinity, modificationProjection, modificationInclusionAtInfinity,
    ← Category.assoc, pullback.condition, Category.assoc, infinitySection_comp_fst,
    Category.comp_id]

/-- The morphism `W'_∞ ⟶ W_∞` of fibres at infinity. -/
def baseChangedInfinityMap :
    modificationFibreAtInfinity (q ≫ f) (baseChangedModification f b q) ⟶
      modificationFibreAtInfinity f b :=
  pullback.lift
    (modificationInclusionAtInfinity (q ≫ f) (baseChangedModification f b q) ≫
      pullback.fst b (familyBaseChange f q))
    (pullback.snd (baseChangedModification f b q) (infinitySection (q ≫ f)) ≫ q)
    (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
        Category.assoc, Category.assoc, (isPullback_infinitySection_familyBaseChange f q).w])

/-- The morphism `W'_∞ ⟶ W_∞` commutes with the inclusions `W'_∞ ⟶ W'` and `W_∞ ⟶ W` and the
projection `W' ⟶ W`. -/
@[reassoc (attr := simp)]
theorem baseChangedInfinityMap_fst :
    baseChangedInfinityMap f b q ≫ modificationInclusionAtInfinity f b =
      modificationInclusionAtInfinity (q ≫ f) (baseChangedModification f b q) ≫
        pullback.fst b (familyBaseChange f q) :=
  pullback.lift_fst _ _ _

/-- The morphism `W'_∞ ⟶ W_∞` lies over `q : X' ⟶ X`. -/
@[reassoc (attr := simp)]
theorem baseChangedInfinityMap_snd :
    baseChangedInfinityMap f b q ≫ pullback.snd b (infinitySection f) =
      pullback.snd (baseChangedModification f b q) (infinitySection (q ≫ f)) ≫ q :=
  pullback.lift_snd _ _ _

/-- A comparison over a square `h` lying over `𝐏¹_{X'} ⟶ 𝐏¹_X` is a base change of `h`'s bottom map
if it is compatible with the projections to `W` and to the corner of `h`. -/
private theorem isPullback_pullback_baseChangedModification {Z Z₀ : Scheme.{u}}
    (c : Z ⟶ projectiveLineProduct (q ≫ f)) (c₀ : Z₀ ⟶ projectiveLineProduct f) (e : Z ⟶ Z₀)
    (h : IsPullback c e (familyBaseChange f q) c₀)
    (L : pullback (baseChangedModification f b q) c ⟶ pullback b c₀)
    (h₁ : L ≫ pullback.fst b c₀ =
      pullback.fst (baseChangedModification f b q) c ≫ pullback.fst b (familyBaseChange f q))
    (h₂ : L ≫ pullback.snd b c₀ = pullback.snd (baseChangedModification f b q) c ≫ e) :
    IsPullback L (pullback.snd (baseChangedModification f b q) c) (pullback.snd b c₀) e := by
  refine IsPullback.of_right ?_ h₂ (IsPullback.of_hasPullback b c₀)
  rw [h₁, ← h.w]
  exact (IsPullback.of_hasPullback (baseChangedModification f b q) c).paste_horiz
    (IsPullback.of_hasPullback b (familyBaseChange f q))

/-- `W'_∞` is the base change `W_∞ ×_X X'`. -/
theorem isPullback_baseChangedInfinityMap :
    IsPullback (baseChangedInfinityMap f b q)
      (modificationProjectionAtInfinity (q ≫ f) (baseChangedModification f b q))
      (modificationProjectionAtInfinity f b) q := by
  rw [modificationProjectionAtInfinity_eq_snd, modificationProjectionAtInfinity_eq_snd]
  exact isPullback_pullback_baseChangedModification f b q _ _ _
    (isPullback_infinitySection_familyBaseChange f q) _ (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _)

/-- The identification `W_∞ ×_X X' ≅ W'_∞` of the base change of the fibre at infinity with the
fibre at infinity of the base change. -/
def baseChangedInfinityIso :
    pullback (modificationProjectionAtInfinity f b) q ≅
      modificationFibreAtInfinity (q ≫ f) (baseChangedModification f b q) :=
  (isPullback_baseChangedInfinityMap f b q).isoPullback.symm

/-- The identification `W_∞ ×_X X' ≅ W'_∞` lies over `X'`. -/
theorem baseChangedInfinityIso_hom_comp :
    (baseChangedInfinityIso f b q).hom ≫
        modificationProjectionAtInfinity (q ≫ f) (baseChangedModification f b q) =
      pullback.snd (modificationProjectionAtInfinity f b) q := by
  rw [baseChangedInfinityIso, Iso.symm_hom, IsPullback.isoPullback_inv_snd]

/-- The identification `W_∞ ×_X X' ≅ W'_∞` followed by `W'_∞ ⟶ W_∞` is the first projection. -/
@[reassoc (attr := simp)]
theorem baseChangedInfinityIso_hom_comp_map :
    (baseChangedInfinityIso f b q).hom ≫ baseChangedInfinityMap f b q =
      pullback.fst (modificationProjectionAtInfinity f b) q := by
  rw [baseChangedInfinityIso, Iso.symm_hom, IsPullback.isoPullback_inv_fst]

/-- `𝐀¹_{X'} ⟶ 𝐀¹_X ⟶ 𝐀¹_S` is `𝐀¹_{X'} ⟶ 𝐀¹_S`. -/
theorem affineLineMap_comp : affineLineMap q ≫ affineLineMap f = affineLineMap (q ≫ f) := by
  refine pullback.hom_ext ?_ ?_ <;> simp

/-- `𝐀¹_{X'}` is the inverse image of `𝐀¹_X` in `𝐏¹_{X'}`. -/
theorem isPullback_projectiveLineAffineChart_familyBaseChange :
    IsPullback (affineLineMap q) (projectiveLineAffineChart (q ≫ f))
      (projectiveLineAffineChart f) (familyBaseChange f q) := by
  have hw : affineLineMap q ≫ projectiveLineAffineChart f =
      projectiveLineAffineChart (q ≫ f) ≫ familyBaseChange f q := by
    refine pullback.hom_ext ?_ ?_
    · simp
    · rw [Category.assoc, Category.assoc, projectiveLineAffineChart_comp_snd,
        familyBaseChange_comp_snd, projectiveLineAffineChart_comp_snd, ← Category.assoc,
        affineLineMap_comp]
  refine IsPullback.of_right ?_ hw (isPullback_projectiveLineAffineChart f)
  rw [affineLineMap_comp, familyBaseChange_comp_snd]
  exact isPullback_projectiveLineAffineChart (q ≫ f)

/-- The morphism `b'⁻¹(𝐀¹_{X'}) ⟶ b⁻¹(𝐀¹_X)` of the opens over the affine charts. -/
def baseChangedChartMap :
    chartOpen (q ≫ f) (baseChangedModification f b q) ⟶ chartOpen f b :=
  pullback.lift (chartInclusion (q ≫ f) (baseChangedModification f b q) ≫
      pullback.fst b (familyBaseChange f q))
    (pullback.snd (baseChangedModification f b q) (projectiveLineAffineChart (q ≫ f)) ≫
      affineLineMap q)
    (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
        Category.assoc, Category.assoc,
        (isPullback_projectiveLineAffineChart_familyBaseChange f q).w])

/-- The morphism `b'⁻¹(𝐀¹_{X'}) ⟶ b⁻¹(𝐀¹_X)` commutes with the open inclusions into `W'` and
`W` and the projection `W' ⟶ W`. -/
@[reassoc (attr := simp)]
theorem baseChangedChartMap_fst :
    baseChangedChartMap f b q ≫ chartInclusion f b =
      chartInclusion (q ≫ f) (baseChangedModification f b q) ≫
        pullback.fst b (familyBaseChange f q) :=
  pullback.lift_fst _ _ _

/-- The morphism `b'⁻¹(𝐀¹_{X'}) ⟶ b⁻¹(𝐀¹_X)` lies over `𝐀¹_{X'} ⟶ 𝐀¹_X`. -/
@[reassoc (attr := simp)]
theorem baseChangedChartMap_snd :
    baseChangedChartMap f b q ≫ pullback.snd b (projectiveLineAffineChart f) =
      pullback.snd (baseChangedModification f b q) (projectiveLineAffineChart (q ≫ f)) ≫
        affineLineMap q :=
  pullback.lift_snd _ _ _

/-- `b'⁻¹(𝐀¹_{X'})` is the base change of `b⁻¹(𝐀¹_X) ⟶ 𝐀¹_X` along `𝐀¹_{X'} ⟶ 𝐀¹_X`. -/
theorem isPullback_baseChangedChartMap_snd :
    IsPullback (baseChangedChartMap f b q)
      (pullback.snd (baseChangedModification f b q) (projectiveLineAffineChart (q ≫ f)))
      (pullback.snd b (projectiveLineAffineChart f)) (affineLineMap q) := by
  exact isPullback_pullback_baseChangedModification f b q _ _ _
    (isPullback_projectiveLineAffineChart_familyBaseChange f q).flip _ (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _)

/-- The base change of `b` is again an isomorphism over the affine chart. -/
theorem isIso_baseChangedModification_chart
    [IsIso (pullback.snd b (projectiveLineAffineChart f))] :
    IsIso (pullback.snd (baseChangedModification f b q) (projectiveLineAffineChart (q ≫ f))) :=
  (isPullback_baseChangedChartMap_snd f b q).flip.isIso_fst_of_isIso

/-- `b'⁻¹(𝐀¹_{X'})` is the base change of `b⁻¹(𝐀¹_X)` along `X' ⟶ X`. -/
theorem isPullback_baseChangedChartMap :
    IsPullback (baseChangedChartMap f b q)
      (chartInclusion (q ≫ f) (baseChangedModification f b q) ≫
        modificationProjection (q ≫ f) (baseChangedModification f b q))
      (chartInclusion f b ≫ modificationProjection f b) q := by
  refine IsPullback.paste_vert (h₂₁ := pullback.fst b (familyBaseChange f q)) ?_
    (isPullback_baseChangedModification f b q)
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback b _).flip
  rw [baseChangedChartMap, pullback.lift_snd, pullback.condition]
  exact (IsPullback.of_hasPullback (baseChangedModification f b q) _).flip.paste_horiz
    (isPullback_projectiveLineAffineChart_familyBaseChange f q)

end Geometry

/-! ### The base change on a test scheme -/

section Test

variable {X X' W S T : Scheme.{u}} (f : X ⟶ S) (b : W ⟶ projectiveLineProduct f) (q : X' ⟶ X)
  (g : T ⟶ X')

/-- The comparison `W' ×_{X'} T ⟶ W ×_X T`, an isomorphism. -/
abbrev baseChangeTestMap :
    pullback (modificationProjection (q ≫ f) (baseChangedModification f b q)) g ⟶
      pullback (modificationProjection f b) (g ≫ q) :=
  pullbackLiftOfIsPullback (isPullback_baseChangedModification f b q) g

/-- The comparison `U' ×_{X'} T ⟶ U ×_X T` of the opens over the affine charts. -/
abbrev baseChangeTestChartMap :
    pullback (chartInclusion (q ≫ f) (baseChangedModification f b q) ≫
        modificationProjection (q ≫ f) (baseChangedModification f b q)) g ⟶
      pullback (chartInclusion f b ≫ modificationProjection f b) (g ≫ q) :=
  pullbackLiftOfIsPullback (isPullback_baseChangedChartMap f b q) g

/-- The comparison `W'_∞ ×_{X'} T ⟶ W_∞ ×_X T` of the fibres at infinity. -/
abbrev baseChangeTestInfinityMap :
    pullback (modificationProjectionAtInfinity (q ≫ f) (baseChangedModification f b q)) g ⟶
      pullback (modificationProjectionAtInfinity f b) (g ≫ q) :=
  pullbackLiftOfIsPullback (isPullback_baseChangedInfinityMap f b q) g

/-- The open `U' ×_{X'} T ⊆ W' ×_{X'} T` is the inverse image of `U ×_X T ⊆ W ×_X T`. -/
theorem isPullback_baseChangeTestChartMap :
    IsPullback
      (openBaseChange (modificationProjection (q ≫ f) (baseChangedModification f b q))
        (chartInclusion (q ≫ f) (baseChangedModification f b q)) g)
      (baseChangeTestChartMap f b q g) (baseChangeTestMap f b q g)
      (openBaseChange (modificationProjection f b) (chartInclusion f b) (g ≫ q)) := by
  refine IsPullback.of_vert_isIso ⟨?_⟩
  refine pullback.hom_ext ?_ ?_
  · simp
  · simp

/-- The base changes of `W'_∞ ⟶ W_∞` and of `W' ⟶ W` commute with the inclusions of the fibres
at infinity. -/
theorem baseChangeTestInfinityMap_comp_modificationInfinityBaseChange :
    baseChangeTestInfinityMap f b q g ≫ modificationInfinityBaseChange f b (g ≫ q) =
      modificationInfinityBaseChange (q ≫ f) (baseChangedModification f b q) g ≫
        baseChangeTestMap f b q g := by
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, pullbackLiftOfIsPullback_fst,
      modificationInfinityBaseChange_comp_fst, pullbackLiftOfIsPullback_fst_assoc,
      baseChangedInfinityMap_fst]
    rw [← Category.assoc (modificationInfinityBaseChange _ _ g),
      modificationInfinityBaseChange_comp_fst, Category.assoc]
  · simp

end Test

section Chow

attribute [local instance] lineInfinityDivisor_isEffectiveCartierDivisor
  isIso_baseChangedModification_chart

variable (C : ChowSituation.{u}) {X X' W : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b] (q : X' ⟶ X) [LocallyOfFiniteType q]
  {T : Scheme.{u}} (g : T ⟶ X')

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType q] in
/-- The comparison `W' ×_{X'} T ⟶ W ×_X T` lies over the base. -/
theorem baseChangeTestMap_comp_testStr :
    baseChangeTestMap f b q g ≫ testStr C f (modificationProjection f b) (g ≫ q) =
      testStr C (q ≫ f) (modificationProjection (q ≫ f) (baseChangedModification f b q)) g := by
  simp only [testStr, pullbackLiftOfIsPullback_fst_assoc]
  rw [← Category.assoc (pullback.fst b (familyBaseChange f q)),
    (isPullback_baseChangedModification f b q).w]
  simp

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType q] in
/-- The comparison of the opens over the affine charts lies over the base. -/
theorem baseChangeTestChartMap_comp_openStr :
    baseChangeTestChartMap f b q g ≫
        openStr C f (modificationProjection f b) (chartInclusion f b) (g ≫ q) =
      openStr C (q ≫ f) (modificationProjection (q ≫ f) (baseChangedModification f b q))
        (chartInclusion (q ≫ f) (baseChangedModification f b q)) g := by
  simp [openStr]

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType q] in
/-- The comparison of the fibres at infinity lies over the base. -/
theorem baseChangeTestInfinityMap_comp_structure :
    baseChangeTestInfinityMap f b q g ≫
        (pullback.fst (modificationProjectionAtInfinity f b) (g ≫ q) ≫
          (modificationProjectionAtInfinity f b ≫ f)) =
      pullback.fst (modificationProjectionAtInfinity (q ≫ f) (baseChangedModification f b q)) g ≫
        (modificationProjectionAtInfinity (q ≫ f) (baseChangedModification f b q) ≫ (q ≫ f)) := by
  rw [pullbackLiftOfIsPullback_fst_assoc, ← Category.assoc (baseChangedInfinityMap f b q),
    (isPullback_baseChangedInfinityMap f b q).w]
  simp

variable [IsIso (pullback.snd b (projectiveLineAffineChart f))] [LocallyOfFiniteType g]

/-- **Lifts and base change.** If `β' ∈ A_{k+1}(W' ×_{X'} T)` restricts over the affine chart to
the flat pullback of `α`, so does its image in `W ×_X T`: the comparison is an isomorphism that
identifies the two opens over the affine charts, and flat pullback commutes with pushforward along
isomorphisms. -/
theorem isLift_baseChangeTestMap {k : ℤ} {α : chowGroup C (g ≫ (q ≫ f)) k}
    {β' : chowGroup C
      (testStr C (q ≫ f) (modificationProjection (q ≫ f) (baseChangedModification f b q)) g)
      (k + 1)}
    (hβ' : IsLift C (q ≫ f) (modificationProjection (q ≫ f) (baseChangedModification f b q))
      (chartInclusion (q ≫ f) (baseChangedModification f b q))
      (relativeDimension_chartInclusion_comp (q ≫ f) (baseChangedModification f b q)) g k α β') :
    IsLift C f (modificationProjection f b) (chartInclusion f b)
      (relativeDimension_chartInclusion_comp f b) (g ≫ q) k
      (chowGroupCongr C (Category.assoc g q f).symm k α)
      (properChowPushforward C
        (testStr C (q ≫ f) (modificationProjection (q ≫ f) (baseChangedModification f b q)) g)
        (testStr C f (modificationProjection f b) (g ≫ q)) (baseChangeTestMap f b q g)
        (baseChangeTestMap_comp_testStr C f b q g) (k + 1)
        (properPushforwardDescends C _ _ _ _ _) β') := by
  have := isOpenImmersion_openBaseChange (modificationProjection f b) (chartInclusion f b) (g ≫ q)
  have := isOpenImmersion_openBaseChange
    (modificationProjection (q ≫ f) (baseChangedModification f b q))
    (chartInclusion (q ≫ f) (baseChangedModification f b q)) g
  unfold IsLift at hβ' ⊢
  rw [chowGroupRestrict_properChowPushforward C
    (testStr C (q ≫ f) (modificationProjection (q ≫ f) (baseChangedModification f b q)) g)
    (testStr C f (modificationProjection f b) (g ≫ q))
    (openStr C (q ≫ f) (modificationProjection (q ≫ f) (baseChangedModification f b q))
      (chartInclusion (q ≫ f) (baseChangedModification f b q)) g)
    (openStr C f (modificationProjection f b) (chartInclusion f b) (g ≫ q))
    (baseChangeTestMap f b q g) (baseChangeTestMap_comp_testStr C f b q g)
    (openBaseChange (modificationProjection (q ≫ f) (baseChangedModification f b q))
      (chartInclusion (q ≫ f) (baseChangedModification f b q)) g)
    (openBaseChange_comp_testStr C (q ≫ f) _ _ g)
    (openBaseChange (modificationProjection f b) (chartInclusion f b) (g ≫ q))
    (openBaseChange_comp_testStr C f _ _ (g ≫ q)) (baseChangeTestChartMap f b q g)
    (baseChangeTestChartMap_comp_openStr C f b q g) (isPullback_baseChangeTestChartMap f b q g)
    (k + 1) (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) β', hβ']
  have h := flatPullbackChow_chowPushforwardOfIso C (g ≫ (q ≫ f))
    (openStr C (q ≫ f) (modificationProjection (q ≫ f) (baseChangedModification f b q))
      (chartInclusion (q ≫ f) (baseChangedModification f b q)) g) ((g ≫ q) ≫ f)
    (openStr C f (modificationProjection f b) (chartInclusion f b) (g ≫ q)) (𝟙 T)
    (by simp) (baseChangeTestChartMap f b q g) (baseChangeTestChartMap_comp_openStr C f b q g)
    (pullback.snd (chartInclusion (q ≫ f) (baseChangedModification f b q) ≫
      modificationProjection (q ≫ f) (baseChangedModification f b q)) g) rfl
    (pullback.snd (chartInclusion f b ≫ modificationProjection f b) (g ≫ q)) rfl
    (by rw [Category.comp_id, pullbackLiftOfIsPullback_snd]) 1
    (relativeDimension_openSnd _ _
      (relativeDimension_chartInclusion_comp (q ≫ f) (baseChangedModification f b q)) g)
    (relativeDimension_openSnd _ _ (relativeDimension_chartInclusion_comp f b) (g ≫ q)) k
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _) α
  rw [chowPushforwardOfIso_id_eq_chowGroupCongr] at h
  exact h.symm

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType q]
  [IsIso (pullback.snd b (projectiveLineAffineChart f))] [LocallyOfFiniteType g] in
/-- On the divisors at infinity of `W' ×_{X'} T` and `W ×_X T`, the comparison of the fibres at
infinity is the morphism of zero schemes induced by the comparison `W' ×_{X'} T ≅ W ×_X T`. -/
theorem testInfinityIso_comp_baseChangeTestInfinityMap
    (E : testInfinityDivisor C (q ≫ f) (baseChangedModification f b q) g =
      pullbackZeroScheme (baseChangeTestMap f b q g)
        (gysinTripleModule (infinityModule f b)
          (pullback.fst (modificationProjection f b) (g ≫ q)))
        (gysinTripleSection (infinityModule f b) (infinitySectionOnW f b)
          (pullback.fst (modificationProjection f b) (g ≫ q)))) :
    testInfinityIso C (q ≫ f) (baseChangedModification f b q) g ≫
        baseChangeTestInfinityMap f b q g =
      eqToHom (congrArg Scheme.IdealSheafData.subscheme E) ≫
        zeroSchemePullbackHom (baseChangeTestMap f b q g)
          (gysinTripleModule (infinityModule f b)
            (pullback.fst (modificationProjection f b) (g ≫ q)))
          (gysinTripleSection (infinityModule f b) (infinitySectionOnW f b)
            (pullback.fst (modificationProjection f b) (g ≫ q))) ≫
        testInfinityIso C f b (g ≫ q) := by
  rw [← cancel_mono (modificationInfinityBaseChange f b (g ≫ q)), Category.assoc, Category.assoc,
    Category.assoc, baseChangeTestInfinityMap_comp_modificationInfinityBaseChange,
    testInfinityIso_comp_modificationInfinityBaseChange,
    ← Category.assoc (testInfinityIso C (q ≫ f) (baseChangedModification f b q) g),
    testInfinityIso_comp_modificationInfinityBaseChange, zeroSchemePullbackHom_subschemeι,
    ← Category.assoc, Stacks.Chow.subschemeι_eqToHom E]

/-- **The cap of the class at infinity of the base change.** On a test scheme `g : T ⟶ X'`,
pushing `C' ∩ α` forward along `W'_∞ ×_{X'} T ≅ W_∞ ×_X T` gives `C ∩ α`. -/
theorem baseChangeTestInfinityMap_cap (k : ℤ) (α : chowGroup C (g ≫ (q ≫ f)) k) :
    properChowPushforward C
        (pullback.fst (modificationProjectionAtInfinity (q ≫ f) (baseChangedModification f b q))
          g ≫ (modificationProjectionAtInfinity (q ≫ f) (baseChangedModification f b q) ≫
            (q ≫ f)))
        (pullback.fst (modificationProjectionAtInfinity f b) (g ≫ q) ≫
          (modificationProjectionAtInfinity f b ≫ f))
        (baseChangeTestInfinityMap f b q g) (baseChangeTestInfinityMap_comp_structure C f b q g)
        (k - 0) (properPushforwardDescends C _ _ _ _ _)
        ((gysinAtInfinityClass C (q ≫ f) (baseChangedModification f b q) inferInstance).cap
          g k α) =
      (gysinAtInfinityClass C f b inferInstance).cap (g ≫ q) k
        (chowGroupCongr C (Category.assoc g q f).symm k α) := by
  obtain ⟨β', hβ'⟩ := exists_isLift C (q ≫ f)
    (modificationProjection (q ≫ f) (baseChangedModification f b q))
    (chartInclusion (q ≫ f) (baseChangedModification f b q))
    (relativeDimension_chartInclusion_comp (q ≫ f) (baseChangedModification f b q)) g k α
  rw [gysinAtInfinityClass_cap_eq_of_isLift C (q ≫ f) (baseChangedModification f b q)
      inferInstance g hβ',
    gysinAtInfinityClass_cap_eq_of_isLift C f b inferInstance (g ≫ q)
      (isLift_baseChangeTestMap C f b q g hβ'),
    properChowPushforward_chowGroupDegreeEquiv_eq C _ _ _ _ (sub_zero k).symm
      (properPushforwardDescends C _ _ _ _ _)]
  refine congrArg (chowGroupDegreeEquiv C _ (sub_zero k).symm) ?_
  have hline : (baseChangeTestMap f b q g ≫ pullback.fst (modificationProjection f b) (g ≫ q)) ≫
      lineMap f b =
      pullback.fst (modificationProjection (q ≫ f) (baseChangedModification f b q)) g ≫
        lineMap (q ≫ f) (baseChangedModification f b q) := by
    simp only [lineMap, pullbackLiftOfIsPullback_fst, Category.assoc, pullback.condition_assoc,
      familyBaseChange_comp_snd]
  have E := zeroScheme_pullback₃_eq (Stacks.Divisors.divisorSheaf (lineInfinityDivisor C.S))
    (Stacks.Divisors.divisorSheafGlobalSection (lineInfinityDivisor C.S))
    (baseChangeTestMap f b q g) (pullback.fst (modificationProjection f b) (g ≫ q)) (lineMap f b)
    (pullback.fst (modificationProjection (q ≫ f) (baseChangedModification f b q)) g)
    (lineMap (q ≫ f) (baseChangedModification f b q)) hline
  rw [gysinSystemOfInvertible_isNaturalUnderProperPushforward C
    (testStr C (q ≫ f) (modificationProjection (q ≫ f) (baseChangedModification f b q)) g)
    (testStr C f (modificationProjection f b) (g ≫ q))
    (baseChangeTestMap f b q g) (baseChangeTestMap_comp_testStr C f b q g)
    (gysinTripleModule (infinityModule f b) (pullback.fst (modificationProjection f b) (g ≫ q)))
    (gysinTripleSection (infinityModule f b) (infinitySectionOnW f b)
      (pullback.fst (modificationProjection f b) (g ≫ q))) k
    (zeroSchemePullbackHom (baseChangeTestMap f b q g) _ _)
    (zeroSchemePullbackHom_subschemeι _ _ _)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) β',
    ← chowPushforwardOfIso_eqToHom_eq_of_heq C
      (testStr C (q ≫ f) (modificationProjection (q ≫ f) (baseChangedModification f b q)) g)
      k E (by rw [← Category.assoc, Stacks.Chow.subschemeι_eqToHom E])
      (onChow_pullback₃_heq C
        (testStr C (q ≫ f) (modificationProjection (q ≫ f) (baseChangedModification f b q)) g)
        (Stacks.Divisors.divisorSheaf (lineInfinityDivisor C.S))
        (Stacks.Divisors.divisorSheafGlobalSection (lineInfinityDivisor C.S)) k β'
        (baseChangeTestMap f b q g) (pullback.fst (modificationProjection f b) (g ≫ q))
        (lineMap f b)
        (pullback.fst (modificationProjection (q ≫ f) (baseChangedModification f b q)) g)
        (lineMap (q ≫ f) (baseChangedModification f b q)) hline).symm]
  exact properChowPushforward_comp_eq_comp₃ C _ _ _ _ _ _ _ _ _ _
    (testInfinityIso_comp_baseChangeTestInfinityMap C f b q g E) _ _ _ _ _ k _ _ _ _ _ _

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType q]
  [IsIso (pullback.snd b (projectiveLineAffineChart f))] [LocallyOfFiniteType g] in
/-- The comparison of the fibres at infinity is inverse to the identification of the restriction
of Remark 0F9Z: `W_∞ ×_X T ≅ (W_∞ ×_X X') ×_{X'} T ≅ W'_∞ ×_{X'} T`. -/
theorem baseChangeTestInfinityMap_comp_restrictionIso :
    baseChangeTestInfinityMap f b q g ≫
        (pullbackLeftPullbackSndIso (modificationProjectionAtInfinity f b) q g).inv ≫
        (transportPullbackIso (pullback.snd (modificationProjectionAtInfinity f b) q)
          (modificationProjectionAtInfinity (q ≫ f) (baseChangedModification f b q))
          (baseChangedInfinityIso f b q) (baseChangedInfinityIso_hom_comp f b q) g).hom =
      𝟙 _ := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, transportPullbackIso_hom_fst, Category.id_comp]
    refine (isPullback_baseChangedInfinityMap f b q).hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, Category.assoc, baseChangedInfinityIso_hom_comp_map,
        pullbackLeftPullbackSndIso_inv_fst, pullbackLiftOfIsPullback_fst]
    · rw [Category.assoc, Category.assoc, Category.assoc, baseChangedInfinityIso_hom_comp,
        pullbackLeftPullbackSndIso_inv_fst_snd, pullbackLiftOfIsPullback_snd_assoc,
        pullback.condition]
  · simp

end Chow

/-! ### Stacks 0GUH -/

section Statement

attribute [local instance] isIso_baseChangedModification_chart

variable (C : ChowSituation.{u}) {X X' W : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b] (q : X' ⟶ X) [LocallyOfFiniteType q]

/-- **Stacks 0GUH.** Let `X` be locally of finite type over the base of chapter 42, let
`b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, and let `C ∈ A⁰(W_∞ ⟶ X)` be the class
of Stacks 0F9J. Let `q : X' ⟶ X` be locally of finite type and let
`b' : W' = W ×_{𝐏¹_X} 𝐏¹_{X'} ⟶ 𝐏¹_{X'}` be the base change of `b`, with fibre at infinity
`i'_∞ : W'_∞ ⟶ W'` (the base change of `i_∞`). Then `b'` is again proper and an isomorphism over
`𝐀¹_{X'}`, and the class `C' ∈ A⁰(W'_∞ ⟶ X')` constructed as in Stacks 0F9J using `b'` is the
restriction `res(C)` of Remark 0F9Z.

The restriction is a class for the chosen fibre product `W_∞ ×_X X' ⟶ X'`; it is read as a class
for `W'_∞ ⟶ X'` along the canonical identification `W_∞ ×_X X' ≅ W'_∞` over `X'`. -/
@[stacks 0GUH]
theorem gysinAtInfinityClass_baseChange
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) :
    haveI := hA
    gysinAtInfinityClass C (q ≫ f) (baseChangedModification f b q) inferInstance =
      bivariantTransport C (gysinSystemOfInvertible C)
        (pullback.fst (modificationProjectionAtInfinity f b) q ≫
          (modificationProjectionAtInfinity f b ≫ f))
        (modificationProjectionAtInfinity (q ≫ f) (baseChangedModification f b q) ≫ (q ≫ f))
        (q ≫ f) (pullback.snd (modificationProjectionAtInfinity f b) q)
        (pullbackSnd_comp_structureMorphism_eq C (modificationProjectionAtInfinity f b ≫ f) f
          (modificationProjectionAtInfinity f b) rfl q)
        (modificationProjectionAtInfinity (q ≫ f) (baseChangedModification f b q)) rfl
        (baseChangedInfinityIso f b q) (baseChangedInfinityIso_hom_comp f b q) 0
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantRestrictionOfInvertible C (modificationProjectionAtInfinity f b ≫ f) f
          (modificationProjectionAtInfinity f b) rfl q 0 (gysinAtInfinityClass C f b hA)) := by
  have := hA
  refine BivariantClass.ext C _ _ _ _ _ _ ?_
  intro T g _ k α
  rw [bivariantTransport_cap, bivariantTransportCap_apply, bivariantRestrictionOfInvertible_cap,
    bivariantRestrictionCap_apply, ← baseChangeTestInfinityMap_cap C f b q g k α]
  change _ = chowPushforwardOfIso C _ _ _ _ (k - 0) (chowPushforwardOfIso C _ _ _ _ (k - 0)
    (chowPushforwardOfIso C _ _ (baseChangeTestInfinityMap f b q g)
      (baseChangeTestInfinityMap_comp_structure C f b q g) (k - 0) _))
  rw [chowPushforwardOfIso_comp_apply, chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_congr_apply C _ _ _ (𝟙 _)
      (by rw [← Category.assoc]; exact baseChangeTestInfinityMap_comp_restrictionIso C f b q g) _
      (Category.id_comp _),
    chowPushforwardOfIso_id]

end Statement

end GysinAtInfinity

end Stacks.Chow

end

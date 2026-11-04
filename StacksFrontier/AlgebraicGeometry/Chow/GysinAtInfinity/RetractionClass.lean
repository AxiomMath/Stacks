module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.Retraction
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.ProperModification
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinClass
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.BaseChangeIsoGysinSystem
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0FAR: the class at infinity retracts the Gysin map at infinity, as bivariant classes

Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over `S`, let
`b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, let `i_∞ : W_∞ ⟶ W` be the fibre at
infinity, `p : W ⟶ X` and `q = p ∘ i_∞ : W_∞ ⟶ X` the projections, and `C ∈ A⁰(W_∞ ⟶ X)` the
class of Stacks 0F9J. Stacks 0FAR asserts

  `C ∘ (W_∞ ⟶ X)_* ∘ i_∞^* = i_∞^*`.

## How the expression types

`i_∞^* ∈ A¹(W_∞ ⟶ W)` is the Gysin class of Stacks 0B79, `(W_∞ ⟶ X)_*` is proper pushforward of
cycle classes and `C ∩ -` is defined on Chow groups of schemes over `X`. The left side is not a
composite of bivariant classes in `A¹(W_∞ ⟶ W)`: Stacks 0EPK pushes a class in `A(W_∞ ⟶ Z)`
forward along a factorization `W_∞ ⟶ Y ⟶ Z`, and `W_∞ ⟶ X` admits no factorization of
`i_∞ : W_∞ ⟶ W` through `X ⟶ W`; nor is `(W'_∞ ⟶ X)_*` defined for a test scheme `W' ⟶ W`
that is not proper. The expression is the operation `β ↦ C ∩ q_*(i_∞^* β)`. It makes sense

* on the test schemes `W ×_X T ⟶ W` for `T ⟶ X` locally of finite type, where it reads
  `A_{k+1}(W ×_X T) ⟶ A_k(W_∞ ×_X T)` — the convention of Stacks 0F9J, whose class `C` caps on
  test schemes over `X`; this is
  `Stacks.Chow.GysinAtInfinity.gysinAtInfinityClass_cap_properChowPushforward_infinityGysin`;
* and, as a bivariant class, on *every* test scheme `t : W' ⟶ W` locally of finite type, once
  `W'` is regarded over `X` through `p ∘ t`. There `q_*` becomes the pushforward along the closed
  immersion `W'_∞ = W_∞ ×_W W' ⟶ W'`, that is the class `i_{∞,*} ∘ i_∞^* ∈ A¹(W ⟶ W)` of
  Stacks 0EPK, and `C` becomes its restriction `res(C) ∈ A⁰(W_∞ ×_X W ⟶ W)` along `p`
  (Stacks 0F9Z). The result lies on `W_∞ ×_X W'`, into which `W'_∞` embeds by the base change of
  the graph `Γ = (1, i_∞) : W_∞ ⟶ W_∞ ×_X W`; so the identity reads

    `res(C) ∘ (i_{∞,*} ∘ i_∞^*) = Γ_* ∘ i_∞^*`   in   `A¹(W_∞ ×_X W ⟶ W)`,

  with `∘` the composition of Stacks 0B75 and `Γ_* ∘ i_∞^*` the pushforward of Stacks 0EPK.

The second reading is the strongest one that type-checks: it is an equality of bivariant
classes, so it holds on every test scheme `W' ⟶ W` and is compatible with all the operations of
Stacks 0B76, and it contains the first one: on `W' = W ×_X T`, pushing both sides forward along
the proper projection `W_∞ ×_X W ×_X T ⟶ W_∞ ×_X T` gives back `C ∩ q_*(i_∞^* β) = i_∞^* β`
(Stacks 0B76 (1) for `C`), because the base change of `Γ` followed by that projection is the
identity of `W_∞ ×_X T`.

## Proof

The source's argument, run over an arbitrary test scheme. For `t : W' ⟶ W` and `α ∈ A_k(W')`,
regard `W'` over `X` and apply the test-scheme form of Stacks 0FAR to the base change of `b` along
`W' ⟶ X` and to the pushforward `σ_* α ∈ A_k(W ×_X W')` of `α` along the graph
`σ = (t, 1) : W' ⟶ W ×_X W'`. Since `i_∞^*` is bivariant, `i_∞^*(σ_* α)` is the pushforward of
`i_∞^* α` along the base change `W'_∞ ⟶ W_∞ ×_X W'` of `σ`, which is the base change of `Γ`;
its pushforward to `W'` is the pushforward of `i_∞^* α` along `W'_∞ ⟶ W'`. This gives
`C ∩ (W'_∞ ⟶ W')_*(i_∞^* α) = Γ'_*(i_∞^* α)`, which is
`gysinAtInfinityClass_cap_properChowPushforward_infinityGysinClass_cap`; the class identity is
this, read through the canonical identifications of the base changes.

## Main definitions

* `Stacks.Chow.GysinAtInfinity.infinityGysinClass` — `i_∞^* ∈ A¹(W_∞ ⟶ W)`, the class of
  Stacks 0B79 of the canonical section of `b^* 𝒪(D_∞)`, on `W_∞`.
* `Stacks.Chow.GysinAtInfinity.infinityGysinPushforwardClass` — `i_{∞,*} ∘ i_∞^* ∈ A¹(W ⟶ W)`.
* `Stacks.Chow.GysinAtInfinity.infinityGraphPushforwardClass` — `Γ_* ∘ i_∞^*`.

## Main results

* `Stacks.Chow.GysinAtInfinity.bivariantCompositeOfInvertible_restriction_gysinAtInfinityClass` —
  the identity of bivariant classes.
* `Stacks.Chow.GysinAtInfinity.gysinAtInfinity_retraction` — **Stacks 0FAR**, in both readings.

## References

* [Stacks Project, Tag 0FAR](https://stacks.math.columbia.edu/tag/0FAR)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B79](https://stacks.math.columbia.edu/tag/0B79)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow.GysinAtInfinity


section Bookkeeping

variable (C : ChowSituation.{u})

/-- Proper pushforward respects heterogeneous equality, in the structure morphisms, the morphism,
the degree and the argument. -/
theorem properChowPushforward_heq_of_heq {A B : Scheme.{u}} {sA sA' : A ⟶ C.S}
    [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] {sB sB' : B ⟶ C.S}
    [LocallyOfFiniteType sB] [LocallyOfFiniteType sB'] (hA : sA = sA') (hB : sB = sB')
    {v v' : A ⟶ B} [IsProper v] [IsProper v'] (hv : v = v') (hvB : v ≫ sB = sA)
    (hvB' : v' ≫ sB' = sA') {k k' : ℤ} (hk : k = k')
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sA sB v hvB k)
    (hfac' : ProperPushforwardFactorsThroughRationalEquivalence C sA' sB' v' hvB' k')
    {x : chowGroup C sA k} {x' : chowGroup C sA' k'} (hx : x ≍ x') :
    properChowPushforward C sA sB v hvB k hfac x ≍
      properChowPushforward C sA' sB' v' hvB' k' hfac' x' := by
  subst hA hB hv hk
  cases hx
  rfl

/-- The cap operation of a class read for an equal morphism and an equal degree is the cap
operation of the class, pushed forward along the comparison of the two base changes. -/
theorem copy_cap_eq_chowPushforwardOfIso (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {v v' : X ⟶ Y}
    [LocallyOfFiniteType v] [LocallyOfFiniteType v'] (h : v = v') (hv : v ≫ sY = sX)
    (hv' : v' ≫ sY = sX) {p p' : ℤ} (hpp : p = p') (c : BivariantClass C G sX sY v hv p)
    {T : Scheme.{u}} (t : T ⟶ Y) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sY) k) :
    (BivariantClass.copy C G sX sY h hv hv' hpp c).cap t k α =
      chowPushforwardOfIso C (pullback.fst v t ≫ sX) (pullback.fst v' t ≫ sX)
        (pullback.congrHom h rfl).hom (by simp) (k - p')
        (chowGroupDegreeEquiv C _ (by rw [hpp]) (c.cap t k α)) := by
  subst h hpp
  rw [chowPushforwardOfIso_congr_apply C _ _ _ (𝟙 _)
    (by ext <;> simp) _ (Category.id_comp _), chowPushforwardOfIso_id]
  rfl

/-- Two composable proper pushforwards are, up to heterogeneous equality, the pushforward along
the composite. -/
theorem properChowPushforward_comp_heq_of_heq {A B D : Scheme.{u}} {sA sA' : A ⟶ C.S}
    [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] {sB : B ⟶ C.S} [LocallyOfFiniteType sB]
    {sD sD' : D ⟶ C.S} [LocallyOfFiniteType sD] [LocallyOfFiniteType sD'] (hA : sA = sA')
    (hD : sD = sD') (v : A ⟶ B) [IsProper v] (w : B ⟶ D) [IsProper w] (z : A ⟶ D) [IsProper z]
    (hvw : v ≫ w = z) (hv : v ≫ sB = sA) (hw : w ≫ sD = sB) (hz : z ≫ sD' = sA') {k k' : ℤ}
    (hk : k = k') (hfacv : ProperPushforwardFactorsThroughRationalEquivalence C sA sB v hv k)
    (hfacw : ProperPushforwardFactorsThroughRationalEquivalence C sB sD w hw k)
    (hfacz : ProperPushforwardFactorsThroughRationalEquivalence C sA' sD' z hz k')
    {x : chowGroup C sA k} {x' : chowGroup C sA' k'} (hx : x ≍ x') :
    properChowPushforward C sB sD w hw k hfacw (properChowPushforward C sA sB v hv k hfacv x) ≍
      properChowPushforward C sA' sD' z hz k' hfacz x' := by
  subst hA hD hk hvw
  cases hx
  exact heq_of_eq (properChowPushforward_comp_apply C sA sB sD v w _ rfl hv hw hz k hfacv hfacw
    hfacz x).symm

/-- A proper pushforward of a class heterogeneously equal to a proper pushforward is, up to
heterogeneous equality, the pushforward along the composite. -/
theorem properChowPushforward_heq_comp_of_heq {A B D : Scheme.{u}} {sA : A ⟶ C.S}
    [LocallyOfFiniteType sA] {sB sB' : B ⟶ C.S} [LocallyOfFiniteType sB]
    [LocallyOfFiniteType sB'] {sD sD' : D ⟶ C.S} [LocallyOfFiniteType sD]
    [LocallyOfFiniteType sD'] (hB : sB = sB') (hD : sD = sD') (z : A ⟶ B) [IsProper z]
    (v : B ⟶ D) [IsProper v] (hz : z ≫ sB' = sA) (hv : v ≫ sD = sB) {k k' : ℤ} (hk : k = k')
    {w : chowGroup C sB k} {x : chowGroup C sA k'}
    (hw : w ≍ properChowPushforward C sA sB' z hz k' (properPushforwardDescends C _ _ _ _ _) x) :
    properChowPushforward C sB sD v hv k (properPushforwardDescends C _ _ _ _ _) w ≍
      properChowPushforward C sA sD' (z ≫ v) (by rw [Category.assoc, ← hD, hv, hB, hz]) k'
        (properPushforwardDescends C _ _ _ _ _) x := by
  subst hB hD hk
  cases eq_of_heq hw
  exact heq_of_eq (properChowPushforward_comp_apply C sA sB sD z v _ rfl hz hv _ k
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) x).symm

end Bookkeeping

attribute [local instance] lineInfinityDivisor_isEffectiveCartierDivisor

section Graph

variable {X W S : Scheme.{u}} (f : X ⟶ S) (b : W ⟶ projectiveLineProduct f)

/-- The fibre at infinity lies over the base through `W`. -/
theorem modificationInclusionAtInfinity_comp_structure :
    modificationInclusionAtInfinity f b ≫ (modificationProjection f b ≫ f) =
      modificationProjectionAtInfinity f b ≫ f :=
  (Category.assoc _ _ _).symm

/-- The graph `W_∞ ⟶ W_∞ ×_X W` of the inclusion of the fibre at infinity. -/
abbrev infinityGraph :
    modificationFibreAtInfinity f b ⟶
      pullback (modificationProjectionAtInfinity f b) (modificationProjection f b) :=
  pullback.lift (𝟙 _) (modificationInclusionAtInfinity f b) (by simp)

/-- If `b` is proper, the graph `W_∞ ⟶ W_∞ ×_X W` is proper. -/
instance isProper_infinityGraph [IsProper b] : IsProper (infinityGraph f b) := by
  have : IsProper (infinityGraph f b ≫
      pullback.fst (modificationProjectionAtInfinity f b) (modificationProjection f b)) := by
    rw [pullback.lift_fst]
    infer_instance
  exact IsProper.of_comp _ (pullback.fst (modificationProjectionAtInfinity f b)
    (modificationProjection f b))

/-- The graph `W_∞ ⟶ W_∞ ×_X W` followed by the second projection is `i_∞`. -/
theorem infinityGraph_comp_snd :
    infinityGraph f b ≫
        pullback.snd (modificationProjectionAtInfinity f b) (modificationProjection f b) =
      modificationInclusionAtInfinity f b :=
  pullback.lift_snd _ _ _


variable {T : Scheme.{u}} (t : T ⟶ W)

/-- The graph `T ⟶ W ×_X T` of a test morphism `t : T ⟶ W`, a section of the projection. -/
abbrev testSection :
    T ⟶ pullback (modificationProjection f b) (t ≫ modificationProjection f b) :=
  pullback.lift t (𝟙 T) (by simp)

/-- If `b` is proper, the graph `T ⟶ W ×_X T` of a test morphism is proper. -/
instance isProper_testSection [IsProper b] : IsProper (testSection f b t) := by
  have : IsProper (testSection f b t ≫
      pullback.snd (modificationProjection f b) (t ≫ modificationProjection f b)) := by
    rw [pullback.lift_snd]
    infer_instance
  exact IsProper.of_comp _ (pullback.snd (modificationProjection f b)
    (t ≫ modificationProjection f b))

/-- The graph `W_∞ ×_W T ⟶ W_∞ ×_X T` over a test morphism `t : T ⟶ W`. -/
abbrev testGraph :
    pullback (modificationInclusionAtInfinity f b) t ⟶
      pullback (modificationProjectionAtInfinity f b) (t ≫ modificationProjection f b) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by
    rw [modificationProjectionAtInfinity, ← Category.assoc, pullback.condition, Category.assoc])

/-- The graph `W_∞ ×_W T ⟶ W_∞ ×_X T` followed by the projection to `T` is the projection
`W_∞ ×_W T ⟶ T`. -/
@[reassoc]
theorem testGraph_snd :
    testGraph f b t ≫
        pullback.snd (modificationProjectionAtInfinity f b) (t ≫ modificationProjection f b) =
      pullback.snd (modificationInclusionAtInfinity f b) t :=
  pullback.lift_snd _ _ _

/-- If `b` is proper, the graph `W_∞ ×_W T ⟶ W_∞ ×_X T` is proper. -/
instance isProper_testGraph [IsProper b] : IsProper (testGraph f b t) := by
  have : IsProper (testGraph f b t ≫
      pullback.snd (modificationProjectionAtInfinity f b) (t ≫ modificationProjection f b)) := by
    rw [testGraph_snd]
    infer_instance
  exact IsProper.of_comp _ (pullback.snd (modificationProjectionAtInfinity f b)
    (t ≫ modificationProjection f b))

/-- The base change of the graph `T ⟶ W ×_X T` to the fibres at infinity. -/
abbrev testSectionInfinity :
    pullback (modificationInclusionAtInfinity f b) t ⟶
      pullback (modificationInclusionAtInfinity f b)
        (pullback.fst (modificationProjection f b) (t ≫ modificationProjection f b)) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ testSection f b t) (by
    rw [Category.assoc, pullback.lift_fst, pullback.condition])

/-- The square formed by the graph `T ⟶ W ×_X T`, its base change to the fibres at infinity, and
the projections from the fibres at infinity is a pullback square. -/
theorem isPullback_testSectionInfinity :
    IsPullback (pullback.snd (modificationInclusionAtInfinity f b) t) (testSectionInfinity f b t)
      (testSection f b t)
      (pullback.snd (modificationInclusionAtInfinity f b)
        (pullback.fst (modificationProjection f b) (t ≫ modificationProjection f b))) := by
  refine IsPullback.of_bot ?_ (pullback.lift_snd _ _ _).symm
    (IsPullback.of_hasPullback _ _).flip
  rw [pullback.lift_fst, pullback.lift_fst]
  exact (IsPullback.of_hasPullback _ _).flip

/-- If `b` is proper, the base change of the graph `T ⟶ W ×_X T` to the fibres at infinity is
proper. -/
instance isProper_testSectionInfinity [IsProper b] : IsProper (testSectionInfinity f b t) :=
  MorphismProperty.of_isPullback (P := @IsProper) (isPullback_testSectionInfinity f b t)
    inferInstance

/-- Under the identification `W_∞ ×_W (W ×_X T) ≅ W_∞ ×_X T`, the base change of the graph
`T ⟶ W ×_X T` to the fibres at infinity is the graph `W_∞ ×_W T ⟶ W_∞ ×_X T`. -/
theorem testSectionInfinity_comp_iso :
    testSectionInfinity f b t ≫ (pullbackRightPullbackFstIso (modificationProjection f b)
        (t ≫ modificationProjection f b) (modificationInclusionAtInfinity f b)).hom =
      testGraph f b t := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullbackRightPullbackFstIso_hom_fst]
    exact (pullback.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm
  · rw [Category.assoc, pullbackRightPullbackFstIso_hom_snd]
    refine ((pullback.lift_snd_assoc _ _ _ _).trans ?_).trans (pullback.lift_snd _ _ _).symm
    rw [Category.assoc, pullback.lift_snd, Category.comp_id]

/-- The identification `T ≅ W ×_W T`. -/
abbrev testIdentitySection : T ⟶ pullback (𝟙 W) t :=
  pullback.lift t (𝟙 T) (by simp)

/-- The morphism `T ⟶ W ×_W T` is an isomorphism. -/
instance isIso_testIdentitySection : IsIso (testIdentitySection t) :=
  ⟨⟨pullback.snd _ _, pullback.lift_snd _ _ _, by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
      exact pullback.condition.symm.trans (Category.comp_id _)
    · rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]⟩⟩

/-- The base change `W_∞ ×_W T ⟶ (W_∞ ×_X W) ×_W T` of the graph of `i_∞`. -/
abbrev testGraphOver :
    pullback (modificationInclusionAtInfinity f b) t ⟶
      pullback (pullback.snd (modificationProjectionAtInfinity f b) (modificationProjection f b))
        t :=
  pullback.lift (pullback.fst _ _ ≫ infinityGraph f b) (pullback.snd _ _) (by
    rw [Category.assoc, infinityGraph_comp_snd, pullback.condition])

/-- If `b` is proper, the base change `W_∞ ×_W T ⟶ (W_∞ ×_X W) ×_W T` of the graph of `i_∞` is
proper. -/
instance isProper_testGraphOver [IsProper b] : IsProper (testGraphOver f b t) := by
  have : IsProper (testGraphOver f b t ≫ pullback.snd
      (pullback.snd (modificationProjectionAtInfinity f b) (modificationProjection f b)) t) := by
    rw [pullback.lift_snd]
    infer_instance
  exact IsProper.of_comp _ (pullback.snd
    (pullback.snd (modificationProjectionAtInfinity f b) (modificationProjection f b)) t)

/-- The graph `W_∞ ×_W T ⟶ W_∞ ×_X T` followed by the projection to `W_∞` is the projection
`W_∞ ×_W T ⟶ W_∞`. -/
@[reassoc]
theorem testGraph_fst :
    testGraph f b t ≫
        pullback.fst (modificationProjectionAtInfinity f b) (t ≫ modificationProjection f b) =
      pullback.fst (modificationInclusionAtInfinity f b) t :=
  pullback.lift_fst _ _ _

/-- The graph `W_∞ ⟶ W_∞ ×_X W` followed by the first projection is the identity. -/
@[reassoc]
theorem infinityGraph_fst :
    infinityGraph f b ≫
        pullback.fst (modificationProjectionAtInfinity f b) (modificationProjection f b) =
      𝟙 _ :=
  pullback.lift_fst _ _ _

/-- The graph `W_∞ ⟶ W_∞ ×_X W` followed by the second projection is `i_∞`. -/
@[reassoc] alias infinityGraph_snd := infinityGraph_comp_snd

/-- The morphism `T ⟶ W ×_W T` followed by the projection to `W` is `t`. -/
@[reassoc]
theorem testIdentitySection_fst : testIdentitySection t ≫ pullback.fst (𝟙 W) t = t :=
  pullback.lift_fst _ _ _

/-- The morphism `T ⟶ W ×_W T` followed by the projection to `T` is the identity. -/
@[reassoc]
theorem testIdentitySection_snd : testIdentitySection t ≫ pullback.snd (𝟙 W) t = 𝟙 T :=
  pullback.lift_snd _ _ _

/-- The morphism `W_∞ ×_W T ⟶ (W_∞ ×_X W) ×_W T` followed by the projection to `W_∞ ×_X W` is
the projection to `W_∞` followed by the graph of `i_∞`. -/
@[reassoc]
theorem testGraphOver_fst :
    testGraphOver f b t ≫
        pullback.fst (pullback.snd (modificationProjectionAtInfinity f b)
          (modificationProjection f b)) t =
      pullback.fst (modificationInclusionAtInfinity f b) t ≫ infinityGraph f b :=
  pullback.lift_fst _ _ _

/-- The morphism `W_∞ ×_W T ⟶ (W_∞ ×_X W) ×_W T` followed by the projection to `T` is the
projection `W_∞ ×_W T ⟶ T`. -/
@[reassoc]
theorem testGraphOver_snd :
    testGraphOver f b t ≫
        pullback.snd (pullback.snd (modificationProjectionAtInfinity f b)
          (modificationProjection f b)) t =
      pullback.snd (modificationInclusionAtInfinity f b) t :=
  pullback.lift_snd _ _ _

/-- The identification `A ×_B D ≅ A ×_{v ≫ 𝟙 B} D` commutes with the first projections. -/
@[reassoc]
theorem congrHom_compId_fst {A B D : Scheme.{u}} (v : A ⟶ B) (w : D ⟶ B) :
    (pullback.congrHom (Category.comp_id v).symm (rfl : w = w)).hom ≫ pullback.fst (v ≫ 𝟙 B) w =
      pullback.fst v w := by
  simp

/-- The identification `A ×_B D ≅ A ×_{v ≫ 𝟙 B} D` commutes with the second projections. -/
@[reassoc]
theorem congrHom_compId_snd {A B D : Scheme.{u}} (v : A ⟶ B) (w : D ⟶ B) :
    (pullback.congrHom (Category.comp_id v).symm (rfl : w = w)).hom ≫ pullback.snd (v ≫ 𝟙 B) w =
      pullback.snd v w := by
  simp

/-- The two readings of the graph `W_∞ ×_W T ⟶ (W_∞ ×_X W) ×_W T` agree. -/
theorem testGraph_comp_comparison_eq
    (hu : testIdentitySection t ≫ (pullback.fst (𝟙 W) t ≫ modificationProjection f b) =
      t ≫ modificationProjection f b) :
    ((testGraph f b t ≫ (testBaseChangeIso (modificationProjectionAtInfinity f b)
        (pullback.fst (𝟙 W) t ≫ modificationProjection f b) (testIdentitySection t)
        (t ≫ modificationProjection f b) hu).hom) ≫
      (pullbackLeftPullbackSndIso (modificationProjectionAtInfinity f b)
        (modificationProjection f b) (pullback.fst (𝟙 W) t)).inv) ≫
      (pullbackRightPullbackFstIso (𝟙 W) t
        (pullback.snd (modificationProjectionAtInfinity f b) (modificationProjection f b))).hom =
      testGraphOver f b t ≫ (pullback.congrHom (Category.comp_id _).symm rfl).hom := by
  refine pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_ <;>
    simp only [Category.assoc, pullbackRightPullbackFstIso_hom_fst_assoc,
      pullbackLeftPullbackSndIso_inv_snd_snd_assoc, testBaseChangeIso_hom_snd_assoc,
      testGraph_snd_assoc, infinityGraph_fst, infinityGraph_snd, testIdentitySection_fst,
      testGraph_fst, testGraph_snd, testGraphOver_fst, testGraphOver_snd, congrHom_compId_fst,
      congrHom_compId_snd, Category.comp_id, testIdentitySection_snd,
      pullbackLeftPullbackSndIso_inv_fst, pullbackRightPullbackFstIso_hom_snd,
      testBaseChangeIso_hom_fst, pullback.condition]

end Graph

variable (C : ChowSituation.{u}) {X W : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]

/-- The bivariant Gysin class `i_∞^* ∈ A¹(W_∞ ⟶ W)` of the fibre at infinity: the class of
Stacks 0B79 of the canonical section of `b^* 𝒪(D_∞)`, read on `W_∞` through the identification of
its zero scheme with the fibre at infinity. -/
def infinityGysinClass :
    BivariantClass C (gysinSystemOfInvertible C) (modificationProjectionAtInfinity f b ≫ f)
      (modificationProjection f b ≫ f) (modificationInclusionAtInfinity f b)
      (modificationInclusionAtInfinity_comp_structure f b) 1 :=
  bivariantTransport C (gysinSystemOfInvertible C)
    (gysinTripleInclusion (infinityModule f b) (infinitySectionOnW f b) ≫
      (modificationProjection f b ≫ f))
    (modificationProjectionAtInfinity f b ≫ f) (modificationProjection f b ≫ f)
    (gysinTripleInclusion (infinityModule f b) (infinitySectionOnW f b)) rfl
    (modificationInclusionAtInfinity f b) (modificationInclusionAtInfinity_comp_structure f b)
    (infinityIso f b) (infinityIso_hom_comp f b) 1
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (gysinBivariantClass C (modificationProjection f b ≫ f) (infinityModule f b)
      (infinitySectionOnW f b)).1


/-- The Gysin map at infinity on `W ×_X T`, `Stacks.Chow.GysinAtInfinity.infinityGysin`, is the
cap of `i_∞^*` at the test scheme `W ×_X T ⟶ W`, read on `W_∞ ×_X T`. -/
theorem infinityGysin_heq_infinityGysinClass_cap {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ)
    (β : chowGroup C (testStr C f (modificationProjection f b) g) (k + 1)) :
    infinityGysin C f b g k β ≍
      chowPushforwardOfIso C
        (pullback.fst (modificationInclusionAtInfinity f b)
          (pullback.fst (modificationProjection f b) g) ≫
            (modificationProjectionAtInfinity f b ≫ f))
        (modificationInfinityBaseChangeOver f b g)
        (pullbackRightPullbackFstIso (modificationProjection f b) g
          (modificationInclusionAtInfinity f b)).hom
        (by rw [pullbackRightPullbackFstIso_hom_fst_assoc]) (k + 1 - 1)
        ((infinityGysinClass C f b).cap (pullback.fst (modificationProjection f b) g) (k + 1)
          β) := by
  have hcap : (infinityGysinClass C f b).cap (pullback.fst (modificationProjection f b) g) (k + 1)
      β = chowPushforwardOfIso C _ _ (transportPullbackIso
        (gysinTripleInclusion (infinityModule f b) (infinitySectionOnW f b))
        (modificationInclusionAtInfinity f b) (infinityIso f b) (infinityIso_hom_comp f b)
        (pullback.fst (modificationProjection f b) g)).hom
        (transportPullbackIso_hom_comp_base C _ _ _ _ rfl _
          (modificationInclusionAtInfinity_comp_structure f b) _ _ _) (k + 1 - 1)
        (gysinBivariantCap C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f)
          (infinityModule f b) (infinitySectionOnW f b)
          (pullback.fst (modificationProjection f b) g) (k + 1) β) := rfl
  rw [hcap, gysinBivariantCap_apply, chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_comp_apply, infinityGysin_apply]
  refine properChowPushforward_heq_of_heq C rfl rfl ?_ _ _ (by omega) _ _ ?_
  · refine pullback.hom_ext ?_ ?_
    · simp [testInfinityIso]
    · simp [testInfinityIso]
  · exact onChow_heq _ _ _ _ (by omega)
      (chowGroupDegreeEquiv_heq C _ _ β).symm

variable (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))


omit [LocallyOfFiniteType f] [IsProper b] in
/-- The graph `W_∞ ×_W T ⟶ W_∞ ×_X T` commutes with the structure morphisms to `S` through
`W_∞`. -/
theorem testGraph_comp_structure {T : Scheme.{u}} (t : T ⟶ W) :
    testGraph f b t ≫ (pullback.fst (modificationProjectionAtInfinity f b)
        (t ≫ modificationProjection f b) ≫ (modificationProjectionAtInfinity f b ≫ f)) =
      pullback.fst (modificationInclusionAtInfinity f b) t ≫
        (modificationProjectionAtInfinity f b ≫ f) :=
  pullback.lift_fst_assoc _ _ _ _

omit [LocallyOfFiniteType f] [IsProper b] in
/-- The two structure morphisms `W_∞ ×_W T ⟶ S`, through `T` and through `W_∞`, agree. -/
theorem pullbackSnd_modificationInclusionAtInfinity_comp_structure {T : Scheme.{u}}
    (t : T ⟶ W) :
    pullback.snd (modificationInclusionAtInfinity f b) t ≫ ((t ≫ modificationProjection f b) ≫ f) =
      pullback.fst (modificationInclusionAtInfinity f b) t ≫
        (modificationProjectionAtInfinity f b ≫ f) := by
  rw [← Category.assoc, ← Category.assoc, ← pullback.condition, Category.assoc, Category.assoc]
  exact congrArg _ (Category.assoc _ _ _).symm

/-- **The retraction on an arbitrary test scheme.** For `t : T ⟶ W` locally of finite type and
`α ∈ A_k(T)`, let `T_∞ = W_∞ ×_W T`. Capping with `C` (at the test scheme `T ⟶ X`) the pushforward
to `T` of `i_∞^* α ∈ A_{k-1}(T_∞)` gives the pushforward of `i_∞^* α` along the graph
`T_∞ ⟶ W_∞ ×_X T`. This is Stacks 0FAR for the base change of `b` along `T ⟶ X`, applied to the
pushforward of `α` along the graph `T ⟶ W ×_X T` of `t`. -/
theorem gysinAtInfinityClass_cap_properChowPushforward_infinityGysinClass_cap
    {T : Scheme.{u}} (t : T ⟶ W) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ (modificationProjection f b ≫ f)) k) :
    (gysinAtInfinityClass C f b hA).cap (t ≫ modificationProjection f b) (k - 1)
        (properChowPushforward C
          (pullback.fst (modificationInclusionAtInfinity f b) t ≫
            (modificationProjectionAtInfinity f b ≫ f))
          ((t ≫ modificationProjection f b) ≫ f)
          (pullback.snd (modificationInclusionAtInfinity f b) t)
          (pullbackSnd_modificationInclusionAtInfinity_comp_structure C f b t) (k - 1)
          (properPushforwardDescends C _ _ _ _ _) ((infinityGysinClass C f b).cap t k α)) =
      chowGroupDegreeEquiv C _ (sub_zero (k - 1)).symm
        (properChowPushforward C
          (pullback.fst (modificationInclusionAtInfinity f b) t ≫
            (modificationProjectionAtInfinity f b ≫ f))
          (pullback.fst (modificationProjectionAtInfinity f b) (t ≫ modificationProjection f b) ≫
            (modificationProjectionAtInfinity f b ≫ f))
          (testGraph f b t) (testGraph_comp_structure C f b t) (k - 1)
          (properPushforwardDescends C _ _ _ _ _) ((infinityGysinClass C f b).cap t k α)) := by
  have hσ : testSection f b t ≫ testStr C f (modificationProjection f b)
      (t ≫ modificationProjection f b) = t ≫ (modificationProjection f b ≫ f) :=
    pullback.lift_fst_assoc _ _ _ _
  set β := properChowPushforward C (t ≫ (modificationProjection f b ≫ f))
    (testStr C f (modificationProjection f b) (t ≫ modificationProjection f b))
    (testSection f b t) hσ (k - 1 + 1) (properPushforwardDescends C _ _ _ _ _)
    (chowGroupDegreeEquiv C _ (by omega : k = k - 1 + 1) α) with hβ
  have hB : infinityGysin C f b (t ≫ modificationProjection f b) (k - 1) β =
      properChowPushforward C
        (pullback.fst (modificationInclusionAtInfinity f b) t ≫
          (modificationProjectionAtInfinity f b ≫ f))
        (pullback.fst (modificationProjectionAtInfinity f b) (t ≫ modificationProjection f b) ≫
          (modificationProjectionAtInfinity f b ≫ f))
        (testGraph f b t) (testGraph_comp_structure C f b t) (k - 1)
        (properPushforwardDescends C _ _ _ _ _) ((infinityGysinClass C f b).cap t k α) := by
    refine eq_of_heq ((infinityGysin_heq_infinityGysinClass_cap C f b _ (k - 1) β).trans ?_)
    rw [hβ, (infinityGysinClass C f b).proper_naturality_of_test_eq
      (pullback.fst (modificationProjection f b) (t ≫ modificationProjection f b))
      (testSection f b t) t (pullback.lift_fst _ _ _) (testSectionInfinity f b t)
      (isPullback_testSectionInfinity f b t) (pullback.lift_fst _ _ _) (k - 1 + 1) hσ
      (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)]
    exact properChowPushforward_comp_heq_of_heq C rfl rfl _ _ _ (testSectionInfinity_comp_iso f b t)
      _ _ _ (by omega) _ _ _ (heq_cap_of_heq C _ _ _ _ _ _ _ t (by omega)
        (chowGroupDegreeEquiv_heq C _ _ α))
  rw [properChowPushforward_comp_apply C _ _ _ (testGraph f b t)
    (pullback.snd (modificationProjectionAtInfinity f b) (t ≫ modificationProjection f b))
    (pullback.snd (modificationInclusionAtInfinity f b) t) (testGraph_snd f b t)
    (testGraph_comp_structure C f b t)
    (modificationInfinityBaseChange_snd_over f b (t ≫ modificationProjection f b)) _ (k - 1)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _), ← hB]
  exact gysinAtInfinityClass_cap_properChowPushforward_infinityGysin C f b
    (t ≫ modificationProjection f b) hA (k - 1) β

/-- The class `i_{∞,*} ∘ i_∞^* ∈ A¹(W ⟶ W)` of Stacks 0EPK: the Gysin class of the fibre at
infinity pushed forward along `i_∞ : W_∞ ⟶ W`. -/
def infinityGysinPushforwardClass :
    BivariantClass C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f)
      (modificationProjection f b ≫ f) (𝟙 W) (Category.id_comp _) 1 :=
  canonicalBivariantProperPushforward C (modificationProjectionAtInfinity f b ≫ f)
    (modificationProjection f b ≫ f) (modificationProjection f b ≫ f)
    (modificationInclusionAtInfinity f b) (𝟙 W)
    (modificationInclusionAtInfinity_comp_structure f b) (Category.id_comp _) 1
    (BivariantClass.copy C (canonicalGysinSystem C) _ _ (Category.comp_id _).symm _ _ rfl
      (infinityGysinClass C f b))

omit [LocallyOfFiniteType f] [IsProper b] in
/-- The composite `W_∞ ×_W T ⟶ T ⟶ W ×_W T` commutes with the structure morphisms to `S`. -/
theorem testIdentitySection_comp_structure {T : Scheme.{u}} (t : T ⟶ W) :
    (pullback.snd (modificationInclusionAtInfinity f b) t ≫ testIdentitySection t) ≫
        (pullback.fst (𝟙 W) t ≫ (modificationProjection f b ≫ f)) =
      pullback.fst (modificationInclusionAtInfinity f b) t ≫
        (modificationProjectionAtInfinity f b ≫ f) := by
  rw [Category.assoc, pullback.lift_fst_assoc, ← Category.assoc, ← pullback.condition,
    Category.assoc]
  exact congrArg _ (Category.assoc _ _ _).symm

/-- The cap of `i_{∞,*} ∘ i_∞^*` on a test scheme `t : T ⟶ W`: the pushforward to `T` of
`i_∞^* ∩ α`. -/
theorem infinityGysinPushforwardClass_cap {T : Scheme.{u}} (t : T ⟶ W) [LocallyOfFiniteType t]
    (k : ℤ) (α : chowGroup C (t ≫ (modificationProjection f b ≫ f)) k) :
    (infinityGysinPushforwardClass C f b).cap t k α =
      properChowPushforward C
        (pullback.fst (modificationInclusionAtInfinity f b) t ≫
          (modificationProjectionAtInfinity f b ≫ f))
        (pullback.fst (𝟙 W) t ≫ (modificationProjection f b ≫ f))
        (pullback.snd (modificationInclusionAtInfinity f b) t ≫ testIdentitySection t)
        (testIdentitySection_comp_structure C f b t) (k - 1)
        (properPushforwardDescends C _ _ _ _ _) ((infinityGysinClass C f b).cap t k α) :=
  canonicalBivariantProperPushforward_copy_cap C _ _ _ _ _ _ _ _ _ _ _ _ t
    (pullback.snd (modificationInclusionAtInfinity f b) t ≫ testIdentitySection t)
    (by rw [Category.assoc, pullback.lift_fst, pullback.condition])
    (by rw [Category.assoc, pullback.lift_snd, Category.comp_id])
    (testIdentitySection_comp_structure C f b t) k α

/-- The class `Γ_* ∘ i_∞^* ∈ A¹(W_∞ ×_X W ⟶ W)` of Stacks 0EPK: the Gysin class of the fibre at
infinity pushed forward along the graph `Γ = (1, i_∞) : W_∞ ⟶ W_∞ ×_X W` of its inclusion. -/
def infinityGraphPushforwardClass :
    BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) (modificationProjection f b) ≫
        (modificationProjectionAtInfinity f b ≫ f))
      (modificationProjection f b ≫ f)
      (pullback.snd (modificationProjectionAtInfinity f b) (modificationProjection f b))
      (pullbackSnd_comp_structureMorphism_eq C (modificationProjectionAtInfinity f b ≫ f) f
          (modificationProjectionAtInfinity f b) rfl (modificationProjection f b)) 1 :=
  canonicalBivariantProperPushforward C (modificationProjectionAtInfinity f b ≫ f)
    (pullback.fst (modificationProjectionAtInfinity f b) (modificationProjection f b) ≫
      (modificationProjectionAtInfinity f b ≫ f))
    (modificationProjection f b ≫ f) (infinityGraph f b)
    (pullback.snd (modificationProjectionAtInfinity f b) (modificationProjection f b))
    (by rw [← Category.assoc, pullback.lift_fst, Category.id_comp])
    (pullbackSnd_comp_structureMorphism_eq C (modificationProjectionAtInfinity f b ≫ f) f
      (modificationProjectionAtInfinity f b) rfl (modificationProjection f b)) 1
    (BivariantClass.copy C (canonicalGysinSystem C) _ _ (infinityGraph_comp_snd f b).symm _ _ rfl
      (infinityGysinClass C f b))


omit [LocallyOfFiniteType f] [IsProper b] in
/-- The morphism `W_∞ ×_W T ⟶ (W_∞ ×_X W) ×_W T` commutes with the structure morphisms to `S`
through `W_∞`. -/
theorem testGraphOver_comp_structure {T : Scheme.{u}} (t : T ⟶ W) :
    testGraphOver f b t ≫
        (pullback.fst (pullback.snd (modificationProjectionAtInfinity f b)
          (modificationProjection f b)) t ≫
            (pullback.fst (modificationProjectionAtInfinity f b) (modificationProjection f b) ≫
              (modificationProjectionAtInfinity f b ≫ f))) =
      pullback.fst (modificationInclusionAtInfinity f b) t ≫
        (modificationProjectionAtInfinity f b ≫ f) := by
  refine (pullback.lift_fst_assoc _ _ _ _).trans ?_
  rw [Category.assoc, ← Category.assoc (infinityGraph f b), pullback.lift_fst, Category.id_comp]

/-- The cap of `Γ_* ∘ i_∞^*` on a test scheme `t : T ⟶ W`: the pushforward of `i_∞^* ∩ α` along
the base change of the graph `Γ`. -/
theorem infinityGraphPushforwardClass_cap {T : Scheme.{u}} (t : T ⟶ W) [LocallyOfFiniteType t]
    (k : ℤ) (α : chowGroup C (t ≫ (modificationProjection f b ≫ f)) k) :
    (infinityGraphPushforwardClass C f b).cap t k α =
      properChowPushforward C
        (pullback.fst (modificationInclusionAtInfinity f b) t ≫
          (modificationProjectionAtInfinity f b ≫ f))
        (pullback.fst (pullback.snd (modificationProjectionAtInfinity f b)
          (modificationProjection f b)) t ≫
            (pullback.fst (modificationProjectionAtInfinity f b) (modificationProjection f b) ≫
              (modificationProjectionAtInfinity f b ≫ f)))
        (testGraphOver f b t) (testGraphOver_comp_structure C f b t) (k - 1)
        (properPushforwardDescends C _ _ _ _ _) ((infinityGysinClass C f b).cap t k α) :=
  canonicalBivariantProperPushforward_copy_cap C _ _ _ _ _ _ _ _ _ _ _ _ t
    (testGraphOver f b t) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    (testGraphOver_comp_structure C f b t) k α

/-- **Stacks 0FAR, as an identity of bivariant classes.** In `A¹(W_∞ ×_X W ⟶ W)`,

  `res(C) ∘ (i_{∞,*} ∘ i_∞^*) = Γ_* ∘ i_∞^*`,

where `res(C) ∈ A⁰(W_∞ ×_X W ⟶ W)` is the restriction of the class `C` of Stacks 0F9J along
`p : W ⟶ X` (Stacks 0F9Z), `i_{∞,*} ∘ i_∞^* ∈ A¹(W ⟶ W)` and `Γ_* ∘ i_∞^*` are the pushforwards
(Stacks 0EPK) of the Gysin class `i_∞^*` of Stacks 0B79 along `i_∞` and along the graph
`Γ = (1, i_∞) : W_∞ ⟶ W_∞ ×_X W`, and `∘` is the composition of Stacks 0B75. The composite is a
class for `pr₂ ≫ 𝟙_W` of degree `0 + 1`, and the right side is read there through
`Stacks.Chow.BivariantClass.copy`. -/
theorem bivariantCompositeOfInvertible_restriction_gysinAtInfinityClass :
    bivariantCompositeOfInvertible C
        (pullback.fst (modificationProjectionAtInfinity f b) (modificationProjection f b) ≫
          (modificationProjectionAtInfinity f b ≫ f))
        (modificationProjection f b ≫ f) (modificationProjection f b ≫ f)
        (pullback.snd (modificationProjectionAtInfinity f b) (modificationProjection f b)) (𝟙 W)
        (pullbackSnd_comp_structureMorphism_eq C (modificationProjectionAtInfinity f b ≫ f) f
          (modificationProjectionAtInfinity f b) rfl (modificationProjection f b))
        (Category.id_comp _) 0 1
        (bivariantRestrictionOfInvertible C (modificationProjectionAtInfinity f b ≫ f) f
          (modificationProjectionAtInfinity f b) rfl (modificationProjection f b) 0
          (gysinAtInfinityClass C f b hA))
        (infinityGysinPushforwardClass C f b) =
      BivariantClass.copy C (gysinSystemOfInvertible C) _ _ (Category.comp_id _).symm _ _
        (zero_add 1).symm (infinityGraphPushforwardClass C f b) := by
  refine BivariantClass.ext C _ _ _ _ _ _ ?_
  intro T t _ k α
  rw [copy_cap_eq_chowPushforwardOfIso, infinityGraphPushforwardClass_cap,
    bivariantCompositeOfInvertible, bivariantComposite_cap, bivariantCompositeCap_apply,
    bivariantRestrictionOfInvertible_cap, bivariantRestrictionCap_apply,
    infinityGysinPushforwardClass_cap]
  have hu : testIdentitySection t ≫ (pullback.fst (𝟙 W) t ≫ modificationProjection f b) =
      t ≫ modificationProjection f b := pullback.lift_fst_assoc _ _ _ _
  have hmb : testIdentitySection t ≫ ((pullback.fst (𝟙 W) t ≫ modificationProjection f b) ≫ f) =
      (t ≫ modificationProjection f b) ≫ f := by
    rw [← Category.assoc, hu]
  have h1 : chowGroupCongr C (Category.assoc _ _ _).symm (k - 1)
      (properChowPushforward C _ _
        (pullback.snd (modificationInclusionAtInfinity f b) t ≫ testIdentitySection t)
        (testIdentitySection_comp_structure C f b t) (k - 1)
        (properPushforwardDescends C _ _ _ _ _) ((infinityGysinClass C f b).cap t k α)) =
      chowPushforwardOfIso C _ _ (testIdentitySection t) hmb (k - 1)
        (properChowPushforward C _ _ (pullback.snd (modificationInclusionAtInfinity f b) t)
          (pullbackSnd_modificationInclusionAtInfinity_comp_structure C f b t) (k - 1)
          (properPushforwardDescends C _ _ _ _ _) ((infinityGysinClass C f b).cap t k α)) :=
    eq_of_heq ((chowGroupCongr_heq C _ _ _).trans
      (properChowPushforward_comp_heq_of_heq C rfl (Category.assoc _ _ _) _ _ _ rfl _ _ _ rfl
        _ _ _ HEq.rfl).symm)
  set x := properChowPushforward C _ _ (pullback.snd (modificationInclusionAtInfinity f b) t)
    (pullbackSnd_modificationInclusionAtInfinity_comp_structure C f b t) (k - 1)
    (properPushforwardDescends C _ _ _ _ _) ((infinityGysinClass C f b).cap t k α) with hx
  rw [h1, (gysinAtInfinityClass C f b hA).cap_chowPushforwardOfIso _ (testIdentitySection t)
    (t ≫ modificationProjection f b) hu _ rfl (k - 1) hmb x x rfl, hx,
    gysinAtInfinityClass_cap_properChowPushforward_infinityGysinClass_cap C f b hA t k α]
  have hz1 : (testGraph f b t ≫ (testBaseChangeIso (modificationProjectionAtInfinity f b)
      (pullback.fst (𝟙 W) t ≫ modificationProjection f b) (testIdentitySection t)
      (t ≫ modificationProjection f b) hu).hom) ≫
        (pullback.fst (modificationProjectionAtInfinity f b)
          (pullback.fst (𝟙 W) t ≫ modificationProjection f b) ≫
            (modificationProjectionAtInfinity f b ≫ f)) =
      pullback.fst (modificationInclusionAtInfinity f b) t ≫
        (modificationProjectionAtInfinity f b ≫ f) := by
    rw [Category.assoc, testBaseChangeIso_hom_fst_assoc]
    exact testGraph_comp_structure C f b t
  have hz2 : ((testGraph f b t ≫ (testBaseChangeIso (modificationProjectionAtInfinity f b)
      (pullback.fst (𝟙 W) t ≫ modificationProjection f b) (testIdentitySection t)
      (t ≫ modificationProjection f b) hu).hom) ≫
      (pullbackLeftPullbackSndIso (modificationProjectionAtInfinity f b)
        (modificationProjection f b) (pullback.fst (𝟙 W) t)).inv) ≫
        (pullback.fst (pullback.snd (modificationProjectionAtInfinity f b)
          (modificationProjection f b)) (pullback.fst (𝟙 W) t) ≫
          (pullback.fst (modificationProjectionAtInfinity f b) (modificationProjection f b) ≫
            (modificationProjectionAtInfinity f b ≫ f))) =
      pullback.fst (modificationInclusionAtInfinity f b) t ≫
        (modificationProjectionAtInfinity f b ≫ f) := by
    rw [Category.assoc, pullbackLeftPullbackSndIso_inv_fst_assoc]
    exact hz1
  refine eq_of_heq ((chowGroupDegreeEquiv_heq C _ _ _).trans ?_)
  refine HEq.trans ?_ (properChowPushforward_heq_comp_of_heq C rfl rfl _ _
    (testGraphOver_comp_structure C f b t) _ (by omega) (chowGroupDegreeEquiv_heq C _ _ _)).symm
  refine HEq.trans ?_ (properChowPushforward_heq_of_heq C rfl rfl
    (testGraph_comp_comparison_eq f b t hu) ?_ _ rfl (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) HEq.rfl)
  refine properChowPushforward_heq_comp_of_heq C rfl rfl _ _ hz2 _ (by omega) ?_
  refine properChowPushforward_heq_comp_of_heq C rfl rfl _ _ hz1 _ (by omega) ?_
  refine properChowPushforward_heq_comp_of_heq C rfl rfl _ _ (testGraph_comp_structure C f b t) _
    (by omega) ?_
  exact chowGroupDegreeEquiv_heq C _ _ _

/-- **Stacks 0FAR.** Let `X` be locally of finite type over the base of chapter 42, let
`b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, let `i_∞ : W_∞ ⟶ W` be the fibre at
infinity, `p : W ⟶ X` the projection and `C ∈ A⁰(W_∞ ⟶ X)` the class of Stacks 0F9J. Then
`C ∘ (W_∞ ⟶ X)_* ∘ i_∞^* = i_∞^*`, in the two readings of the module docstring:

1. as bivariant classes over `W`, valid on every test scheme `W' ⟶ W`:
   `res(C) ∘ (i_{∞,*} ∘ i_∞^*) = Γ_* ∘ i_∞^*` in `A¹(W_∞ ×_X W ⟶ W)`, with `res` the restriction
   of Stacks 0F9Z along `p`, `i_∞^*` the Gysin class of Stacks 0B79, the pushforwards those of
   Stacks 0EPK along `i_∞` and along the graph `Γ : W_∞ ⟶ W_∞ ×_X W`, and `∘` that of
   Stacks 0B75;
2. as the operation of the source on the test schemes `W ×_X T`, `T ⟶ X` locally of finite type:
   for `β ∈ A_{k+1}(W ×_X T)`, `C ∩ (W_∞ ×_X T ⟶ T)_*(i_∞^* β) = i_∞^* β` in `A_k(W_∞ ×_X T)`,
   with `C ∩ -` landing in degree `k - 0`, identified with `k`. -/
@[stacks 0FAR "C ∘ (W_∞ → X)_* ∘ i_∞^* = i_∞^*: as bivariant classes over W, \
res(C) ∘ (i_∞,* ∘ i_∞^*) = Γ_* ∘ i_∞^* in A¹(W_∞ ×_X W → W), on every test scheme W' → W; \
and as the operation β ↦ C ∩ (W_∞ → X)_* i_∞^* β on A_{k+1}(W ×_X T) for T → X"]
theorem gysinAtInfinity_retraction :
    bivariantCompositeOfInvertible C
        (pullback.fst (modificationProjectionAtInfinity f b) (modificationProjection f b) ≫
          (modificationProjectionAtInfinity f b ≫ f))
        (modificationProjection f b ≫ f) (modificationProjection f b ≫ f)
        (pullback.snd (modificationProjectionAtInfinity f b) (modificationProjection f b)) (𝟙 W)
        (pullbackSnd_comp_structureMorphism_eq C (modificationProjectionAtInfinity f b ≫ f) f
          (modificationProjectionAtInfinity f b) rfl (modificationProjection f b))
        (Category.id_comp _) 0 1
        (bivariantRestrictionOfInvertible C (modificationProjectionAtInfinity f b ≫ f) f
          (modificationProjectionAtInfinity f b) rfl (modificationProjection f b) 0
          (gysinAtInfinityClass C f b hA))
        (infinityGysinPushforwardClass C f b) =
      BivariantClass.copy C (gysinSystemOfInvertible C) _ _ (Category.comp_id _).symm _ _
        (zero_add 1).symm (infinityGraphPushforwardClass C f b) ∧
    ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
      (β : chowGroup C (testStr C f (modificationProjection f b) g) (k + 1)),
      (gysinAtInfinityClass C f b hA).cap g k
          (properChowPushforward C (modificationInfinityBaseChangeOver f b g) (g ≫ f)
            (pullback.snd (modificationProjectionAtInfinity f b) g)
            (modificationInfinityBaseChange_snd_over f b g) k
            (properPushforwardDescends C _ _ _ _ _) (infinityGysin C f b g k β)) =
        chowGroupDegreeEquiv C _ (sub_zero k).symm (infinityGysin C f b g k β) :=
  ⟨bivariantCompositeOfInvertible_restriction_gysinAtInfinityClass C f b hA,
    fun g _ k β ↦ gysinAtInfinityClass_cap_properChowPushforward_infinityGysin C f b g hA k β⟩

end Stacks.Chow.GysinAtInfinity

end

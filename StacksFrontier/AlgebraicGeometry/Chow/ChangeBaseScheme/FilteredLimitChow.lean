module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.ChowPullback
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FlatBaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FilteredLimitCycles
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FilteredLimitProjectiveLine
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.GeometricRationalEquivalence
public import StacksCore.Tactic.StacksAttribute

/-!
# Chow groups under a filtered limit of base schemes

In the situation of Stacks 0FVQ the base-change homomorphism on Chow groups of Stacks 0FVJ is
transported along an identification of the base change, giving homomorphisms
`CH_k(X_i) ⟶ CH_k(X')` and `CH_k(X_j) ⟶ CH_k(X_i)` attached to the projections from the limit
base and to the transition morphisms of the inverse system. Every `k`-cycle class on `X'` comes
from a finite stage, and a class on `X_j` dying on `X'` already dies at a finite stage.

## Main definitions

* `Stacks.Chow.baseChangeChowPullbackOfIsPullback` — the base-change homomorphism on Chow groups
  for a flat base change with vanishing dimension shift, written for an arbitrary cartesian
  square realizing the base change rather than for the chosen fibre product.
* `Stacks.Chow.FilteredBaseChangeSystem.stageChowPullback` — the homomorphism
  `CH_k(X_i) ⟶ CH_k(X')`.
* `Stacks.Chow.FilteredBaseChangeSystem.transitionChowPullback` — the homomorphism
  `CH_k(X_j) ⟶ CH_k(X_i)` attached to a transition `i ⟶ j`.

## Main results

* `Stacks.Chow.FilteredBaseChangeSystem.stageCyclePullback_apply`,
  `Stacks.Chow.FilteredBaseChangeSystem.transitionCyclePullback_apply` — the comparison maps on
  cycle groups read coefficientwise on `X'` and on `X_i` themselves.
* `Stacks.Chow.FilteredBaseChangeSystem.transitionCyclePullback_comp`,
  `Stacks.Chow.FilteredBaseChangeSystem.stageCyclePullback_transitionCyclePullback` — the
  comparison maps on cycle groups are functorial.
* `Stacks.Chow.FilteredBaseChangeSystem.exists_stageChowPullback_eq` — **Stacks 0FVQ**,
  surjectivity for Chow groups.
* `Stacks.Chow.FilteredBaseChangeSystem.exists_transitionChowPullback_eq_zero` —
  **Stacks 0FVQ**, eventual injectivity for Chow groups.

## Implementation notes

The base-change homomorphism of `Stacks.Chow.baseChangeChowPullback` lands in the Chow group of
the chosen fibre product `X ×_S S'`. In the filtered situation the relevant base change is
presented by a different cartesian square, so the homomorphism is composed with the pushforward
along the comparison isomorphism; being an isomorphism over the base, that pushforward needs no
instance of Stacks 02S2, by
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isIso`.

Surjectivity on Chow groups is inherited from surjectivity on cycle groups: a class on `X'` is
the class of a cycle, that cycle is the base change of a cycle on some `X_i`, and the
comparison map carries the class of the latter to the class of the former.

Eventual injectivity on Chow groups never descends a rational function. A rational equivalence
on `X'` is presented by Stacks 02S4 part (4) as the total fibre difference of a family of
integral closed subschemes of `X' ×_{S'} 𝐏¹_{S'}`, and closed subschemes descend along the
filtered limit while orders of vanishing need not. The family is finite because `X'` is
quasi-compact, so one stage carries all of its members, and what remains after subtracting the
descended rational equivalence is a cycle killed by base change, which eventual injectivity on
cycle groups kills at a further stage.

## References

* [Stacks Project, Tag 0FVQ](https://stacks.math.columbia.edu/tag/0FVQ)
* [Stacks Project, Tag 0FVG](https://stacks.math.columbia.edu/tag/0FVG)
* [Stacks Project, Tag 0FVJ](https://stacks.math.columbia.edu/tag/0FVJ)
* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w v u

namespace Stacks.Chow

/-! ### Base change on Chow groups along an arbitrary cartesian square -/

/-- The base-change homomorphism `CH_k(X) ⟶ CH_k(Y)` of Chow groups attached to a flat base
change of Chow situations with vanishing dimension shift and to a cartesian square realizing
`Y` as the base change of `X`. -/
def baseChangeChowPullbackOfIsPullback (B : FlatBaseChangeSituation.{u}) (hc : B.c = 0)
    {X Y : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f] {p : Y ⟶ X}
    {q : Y ⟶ B.baseChange.S} [LocallyOfFiniteType q] (sq : IsPullback p q f B.g) (k : ℤ) :
    chowGroup B.base f k →+ chowGroup B.baseChange q k :=
  (chowPushforwardOfIso B.baseChange (pullback.snd f B.g) q sq.isoPullback.inv
      (isoPullback_inv_comp_snd B f sq) k).comp
    (((chowGroupCongrDegree B.baseChange (pullback.snd f B.g)
        (show k + B.c = k by rw [hc, add_zero])).toAddMonoidHom).comp
      (baseChangeChowPullback B f k))

/-- The base-change homomorphism on Chow groups along an arbitrary cartesian square sends the
class of a cycle to the class of the base change of that cycle. -/
theorem baseChangeChowPullbackOfIsPullback_mk (B : FlatBaseChangeSituation.{u}) (hc : B.c = 0)
    {X Y : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f] {p : Y ⟶ X}
    {q : Y ⟶ B.baseChange.S} [LocallyOfFiniteType q] (sq : IsPullback p q f B.g) (k : ℤ)
    (z : CycleGroup B.base f k) :
    baseChangeChowPullbackOfIsPullback B hc f sq k
        (QuotientAddGroup.mk' (rationalEquivalences B.base f k) z) =
      QuotientAddGroup.mk' (rationalEquivalences B.baseChange q k)
        (baseChangeCyclePullbackOfIsPullback B hc f sq k z) := by
  change (chowPushforwardOfIso B.baseChange (pullback.snd f B.g) q sq.isoPullback.inv
      (isoPullback_inv_comp_snd B f sq) k)
    (chowGroupCongrDegree B.baseChange (pullback.snd f B.g)
      (show k + B.c = k by rw [hc, add_zero])
      (baseChangeChowPullback B f k
        (QuotientAddGroup.mk' (rationalEquivalences B.base f k) z))) = _
  rw [baseChangeChowPullback_mk B f k z, chowGroupCongrDegree_mk, chowPushforwardOfIso_mk]
  rfl

/-! ### Composition of base changes along cartesian squares -/

/-- The composite of the base-change homomorphisms on cycle groups of two composable flat base
changes with vanishing dimension shift, read coefficientwise: the coefficient of the cycle at
the image point under the composite, times the multiplicity for the composite. This is Stacks
0FVP part (2) with both dimension shifts zero. -/
private theorem baseChangeCyclePullbackOfIsPullback_comp_apply
    (B : FlatBaseChangeSituation.{u}) (hB : B.c = 0) (C : ChowSituation.{u})
    (g' : C.S ⟶ B.baseChange.S) [Flat g']
    (hg' : ∀ (t : B.baseChange.S) (t' : genericPoints (g' ⁻¹' {t} : Set C.S)),
      C.dimensionFunction t'.1.1 = B.baseChange.dimensionFunction t + 0)
    {X Y Y'' : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f]
    {p : Y ⟶ X} {q : Y ⟶ B.baseChange.S} [LocallyOfFiniteType q] (sq : IsPullback p q f B.g)
    {p' : Y'' ⟶ Y} {q' : Y'' ⟶ C.S} [LocallyOfFiniteType q'] (sq' : IsPullback p' q' q g')
    (k : ℤ) (z : CycleGroup B.base f k) (y : Y'') :
    (baseChangeCyclePullbackOfIsPullback (FlatBaseChangeSituation.second B C g' 0 hg') rfl q sq'
        k (baseChangeCyclePullbackOfIsPullback B hB f sq k z)).1 y =
      z.1 ((p' ≫ p).base y) * flatPullbackWeight C q' (p' ≫ p) k y := by
  have hcomp := baseChangeCyclePullbackSquare_comp_apply B C g' 0 hg' f sq sq' k z y
  rw [baseChangeCyclePullbackSquare_apply (FlatBaseChangeSituation.second B C g' 0 hg') q sq'
      (k + B.c) _ y,
    baseChangeCyclePullbackSquare_apply B f sq k z (p'.base y),
    baseChangeCyclePullbackSquare_apply (FlatBaseChangeSituation.comp B C g' 0 hg') f
      (sq'.paste_horiz sq) k z y, hB] at hcomp
  rw [baseChangeCyclePullbackOfIsPullback_apply'
      (FlatBaseChangeSituation.second B C g' 0 hg') rfl q sq' k _ y,
    baseChangeCyclePullbackOfIsPullback_apply' B hB f sq k z (p'.base y),
    Scheme.Hom.comp_apply]
  simpa only [FlatBaseChangeSituation.second_c, FlatBaseChangeSituation.comp_c,
    FlatBaseChangeSituation.second_baseChange, FlatBaseChangeSituation.comp_baseChange,
    hB, add_zero, zero_add, Scheme.Hom.comp_apply] using hcomp

/-! ### Closed subschemes along a cartesian square -/

/-- **The inverse image of a closed subscheme along a cartesian square.** In a cartesian square
whose two horizontal morphisms are closed immersions, the inverse image along the vertical
morphism of ambient schemes of the ideal sheaf of one is the ideal sheaf of the other. -/
private theorem ker_comap_of_isPullback {A B P Q : Scheme.{u}} {a : A ⟶ P} {p : A ⟶ B}
    {q : P ⟶ Q} {b : B ⟶ Q} [IsClosedImmersion a] [IsClosedImmersion b]
    (sq : IsPullback a p q b) : b.ker.comap q = a.ker := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion b q, ← sq.isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

/-- **Non-containment in a constant section descends along a commuting square.** The inverse
image of a closed subscheme of `X ×_S 𝐏¹_S` along the morphism of families attached to a
commuting square is contained in the constant section at an integral point as soon as that
closed subscheme is: the two sections have the same coordinate on `𝐏¹_ℤ`. -/
private theorem notSubset_range_constantSection_of_square {X Y S S' : Scheme.{u}} (f : X ⟶ S)
    (g : S' ⟶ S) {p : Y ⟶ X} {q : Y ⟶ S'} (w : p ≫ f = q ≫ g)
    (V : (projectiveLineProduct f).IdealSheafData)
    (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ))
    {W : (projectiveLineProduct q).IdealSheafData} (hW : baseChangedFamilyOfSquare f g w V = W)
    (hV : ¬ Set.range W.subschemeι ⊆ Set.range (constantSection q e)) :
    ¬ Set.range V.subschemeι ⊆ Set.range (constantSection f e) := by
  subst hW
  refine fun hsub ↦ hV ?_
  have hrange : Set.range (baseChangedFamilyOfSquare f g w V).subschemeι =
      projectiveLineProductMap f g w ⁻¹' Set.range V.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.range_subschemeι,
      baseChangedFamilyOfSquare, Scheme.IdealSheafData.support_comap]
    rfl
  rw [hrange, range_constantSection]
  intro y hy
  have hpt : projectiveLineProjection f (projectiveLineProductMap f g w y) =
      projectiveLineProjection q y := by
    simpa only [Scheme.Hom.comp_apply] using congrArg
      (fun m : projectiveLineProduct q ⟶ projectiveLine (ULift.{u} ℤ) ↦ m.base y)
      (projectiveLineProductMap_comp_projection f g w)
  have h := hsub hy
  rw [range_constantSection, Set.mem_preimage] at h
  rwa [Set.mem_preimage, ← hpt]

/-! ### Relative dimension at the generic points of an integral member -/

/-- For an integral closed subscheme of a family of projective lines, an equality of
delta-dimensions over the base is an equality of relative dimensions at every generic point:
there is only one generic point. -/
private theorem relativeDimension_familyBase_of_schemeDeltaDimension (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (W : (projectiveLineProduct f).IdealSheafData) [IsIntegral W.subscheme] {n : ℤ}
    (h : schemeDeltaDimension C (familyBase f W) = (n : EInt))
    (ξ : genericPoints W.subscheme) :
    relativeDimension C.dimensionFunction (familyBase f W) ξ.1 = n := by
  obtain ⟨x, hx⟩ := ξ
  rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
  subst hx
  exact WithBotTop.coe_injective
    ((schemeDeltaDimension_eq_genericPoint C (familyBase f W)).symm.trans h)

namespace FilteredBaseChangeSystem

variable {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
  (s : FilteredBaseChangeSystem.{w, v, u} I)

/-! ### Coefficients of the comparison maps on cycle groups -/

/-- The coefficient of the base change of a cycle to the limit base, read on `X'`: the
coefficient of the cycle at the image point in `X_i`, times the multiplicity of the point in the
inverse image of the reduced closure of that image. -/
theorem stageCyclePullback_apply (i : I) (k : ℤ)
    (z : CycleGroup (s.stageSituation i) (pullback.snd s.X.hom (s.stageToBase i)) k)
    (y : (pullback s.X.hom s.limitBaseChange.g : Scheme.{u})) :
    (s.stageCyclePullback i k z).1 y =
      z.1 ((s.stageProjection i).base y) *
        flatPullbackWeight s.limitBaseChange.baseChange
          (pullback.snd s.X.hom s.limitBaseChange.g) (s.stageProjection i) k y :=
  baseChangeCyclePullbackOfIsPullback_apply' (s.stageToLimitBaseChange i) rfl
    (pullback.snd s.X.hom (s.stageToBase i)) (s.isPullback_stageProjection i) k z y

/-- The coefficient of the base change of a cycle along a transition morphism of the inverse
system of bases, read on `X_i`. -/
theorem transitionCyclePullback_apply {i j : I} (f : i ⟶ j) (k : ℤ)
    (z : CycleGroup (s.stageSituation j) (pullback.snd s.X.hom (s.stageToBase j)) k)
    (y : (pullback s.X.hom (s.stageToBase i) : Scheme.{u})) :
    (s.transitionCyclePullback f k z).1 y =
      z.1 ((s.stageTransition f).base y) *
        flatPullbackWeight (s.stageSituation i)
          (pullback.snd s.X.hom (s.stageToBase i)) (s.stageTransition f) k y :=
  baseChangeCyclePullbackOfIsPullback_apply' (s.transitionBaseChange f) rfl
    (pullback.snd s.X.hom (s.stageToBase j)) (s.isPullback_stageTransition f) k z y

/-! ### Functoriality of the comparison maps on cycle groups -/

/-- The base change of `X` along the identity transition is the identity. -/
theorem stageTransition_id (i : I) : s.stageTransition (𝟙 i) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [s.stageTransition_comp_fst (𝟙 i), Category.id_comp]
  · rw [s.stageTransition_comp_snd (𝟙 i), s.diagram.map_id, Category.comp_id, Category.id_comp]

/-- The base changes of `X` along the transitions compose. -/
theorem stageTransition_comp {i j l : I} (f : i ⟶ j) (g : j ⟶ l) :
    s.stageTransition f ≫ s.stageTransition g = s.stageTransition (f ≫ g) := by
  apply pullback.hom_ext
  · rw [Category.assoc, s.stageTransition_comp_fst g, s.stageTransition_comp_fst f,
      s.stageTransition_comp_fst (f ≫ g)]
  · rw [Category.assoc, s.stageTransition_comp_snd g, ← Category.assoc,
      s.stageTransition_comp_snd f, s.stageTransition_comp_snd (f ≫ g), Category.assoc,
      s.diagram.map_comp]

/-- The comparison homomorphisms on cycle groups along the transitions compose. -/
theorem transitionCyclePullback_comp {i j l : I} (f : i ⟶ j) (g : j ⟶ l) (k : ℤ)
    (z : CycleGroup (s.stageSituation l) (pullback.snd s.X.hom (s.stageToBase l)) k) :
    s.transitionCyclePullback f k (s.transitionCyclePullback g k z) =
      s.transitionCyclePullback (f ≫ g) k z := by
  have : Flat (s.diagram.map f) := s.transitionFlat f
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y => ?_)
  calc (s.transitionCyclePullback f k (s.transitionCyclePullback g k z)).1 y
      = z.1 ((s.stageTransition f ≫ s.stageTransition g).base y) *
          flatPullbackWeight (s.stageSituation i) (pullback.snd s.X.hom (s.stageToBase i))
            (s.stageTransition f ≫ s.stageTransition g) k y :=
        baseChangeCyclePullbackOfIsPullback_comp_apply (s.transitionBaseChange g) rfl
          (s.stageSituation i) (s.diagram.map f)
          (s.transitionBaseChange f).dimensionFunction_eq_add
          (pullback.snd s.X.hom (s.stageToBase l)) (s.isPullback_stageTransition g)
          (s.isPullback_stageTransition f) k z y
    _ = (s.transitionCyclePullback (f ≫ g) k z).1 y := by
        rw [s.stageTransition_comp f g]
        exact (baseChangeCyclePullbackOfIsPullback_apply' (s.transitionBaseChange (f ≫ g)) rfl
          (pullback.snd s.X.hom (s.stageToBase l)) (s.isPullback_stageTransition (f ≫ g))
          k z y).symm

/-- The comparison homomorphism to the limit absorbs the comparison homomorphism along a
transition. -/
theorem stageCyclePullback_transitionCyclePullback {i j : I} (f : i ⟶ j) (k : ℤ)
    (z : CycleGroup (s.stageSituation j) (pullback.snd s.X.hom (s.stageToBase j)) k) :
    s.stageCyclePullback i k (s.transitionCyclePullback f k z) = s.stageCyclePullback j k z := by
  have : Flat (s.limitProjection i) := s.flat_limitProjection i
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y => ?_)
  calc (s.stageCyclePullback i k (s.transitionCyclePullback f k z)).1 y
      = z.1 ((s.stageProjection i ≫ s.stageTransition f).base y) *
          flatPullbackWeight s.limitBaseChange.baseChange
            (pullback.snd s.X.hom s.limitBaseChange.g)
            (s.stageProjection i ≫ s.stageTransition f) k y :=
        baseChangeCyclePullbackOfIsPullback_comp_apply (s.transitionBaseChange f) rfl
          s.limitBaseChange.baseChange (s.limitProjection i)
          (s.stageToLimitBaseChange i).dimensionFunction_eq_add
          (pullback.snd s.X.hom (s.stageToBase j)) (s.isPullback_stageTransition f)
          (s.isPullback_stageProjection i) k z y
    _ = (s.stageCyclePullback j k z).1 y := by
        rw [s.stageProjection_comp_stageTransition f]
        exact (baseChangeCyclePullbackOfIsPullback_apply' (s.stageToLimitBaseChange j) rfl
          (pullback.snd s.X.hom (s.stageToBase j)) (s.isPullback_stageProjection j) k z y).symm

/-! ### The homomorphisms on Chow groups -/

/-- The homomorphism `CH_k(X_i) ⟶ CH_k(X')` on Chow groups induced by the projection from the
limit base to the stage `i`. -/
def stageChowPullback (i : I) (k : ℤ) :
    chowGroup (s.stageSituation i) (pullback.snd s.X.hom (s.stageToBase i)) k →+
      chowGroup s.limitBaseChange.baseChange (pullback.snd s.X.hom s.limitBaseChange.g) k :=
  baseChangeChowPullbackOfIsPullback (s.stageToLimitBaseChange i) rfl
    (pullback.snd s.X.hom (s.stageToBase i)) (s.isPullback_stageProjection i) k

/-- The homomorphism `CH_k(X_j) ⟶ CH_k(X_i)` on Chow groups induced by a transition morphism
`i ⟶ j` of the inverse system of bases. -/
def transitionChowPullback {i j : I} (f : i ⟶ j) (k : ℤ) :
    chowGroup (s.stageSituation j) (pullback.snd s.X.hom (s.stageToBase j)) k →+
      chowGroup (s.stageSituation i) (pullback.snd s.X.hom (s.stageToBase i)) k :=
  baseChangeChowPullbackOfIsPullback (s.transitionBaseChange f) rfl
    (pullback.snd s.X.hom (s.stageToBase j)) (s.isPullback_stageTransition f) k

/-- The comparison map to the limit sends the class of a cycle on `X_i` to the class of its base
change to `X'`. -/
theorem stageChowPullback_mk (i : I) (k : ℤ)
    (z : CycleGroup (s.stageSituation i) (pullback.snd s.X.hom (s.stageToBase i)) k) :
    s.stageChowPullback i k (QuotientAddGroup.mk'
        (rationalEquivalences (s.stageSituation i)
          (pullback.snd s.X.hom (s.stageToBase i)) k) z) =
      QuotientAddGroup.mk'
        (rationalEquivalences s.limitBaseChange.baseChange
          (pullback.snd s.X.hom s.limitBaseChange.g) k) (s.stageCyclePullback i k z) :=
  baseChangeChowPullbackOfIsPullback_mk (s.stageToLimitBaseChange i) rfl
    (pullback.snd s.X.hom (s.stageToBase i)) (s.isPullback_stageProjection i) k z

/-- The comparison map along a transition sends the class of a cycle on `X_j` to the class of its
base change to `X_i`. -/
theorem transitionChowPullback_mk {i j : I} (f : i ⟶ j) (k : ℤ)
    (z : CycleGroup (s.stageSituation j) (pullback.snd s.X.hom (s.stageToBase j)) k) :
    s.transitionChowPullback f k (QuotientAddGroup.mk'
        (rationalEquivalences (s.stageSituation j)
          (pullback.snd s.X.hom (s.stageToBase j)) k) z) =
      QuotientAddGroup.mk'
        (rationalEquivalences (s.stageSituation i)
          (pullback.snd s.X.hom (s.stageToBase i)) k) (s.transitionCyclePullback f k z) :=
  baseChangeChowPullbackOfIsPullback_mk (s.transitionBaseChange f) rfl
    (pullback.snd s.X.hom (s.stageToBase j)) (s.isPullback_stageTransition f) k z

/-! ### Surjectivity on Chow groups -/

/-- **Stacks Project, Tag 0FVQ, surjectivity for Chow groups.** Every `k`-cycle class on `X'` is
the image of a `k`-cycle class on `X_i` for some finite stage `i`. -/
@[stacks 0FVQ "Chow groups, surjectivity: every k-cycle class on X' comes from some X_i"]
theorem exists_stageChowPullback_eq (k : ℤ)
    (α : chowGroup s.limitBaseChange.baseChange
      (pullback.snd s.X.hom s.limitBaseChange.g) k) :
    ∃ (i : I) (β : chowGroup (s.stageSituation i)
      (pullback.snd s.X.hom (s.stageToBase i)) k),
      s.stageChowPullback i k β = α := by
  obtain ⟨z, hz⟩ := QuotientAddGroup.mk'_surjective
    (rationalEquivalences s.limitBaseChange.baseChange
      (pullback.snd s.X.hom s.limitBaseChange.g) k) α
  obtain ⟨i, w, hw⟩ := s.exists_stageCyclePullback_eq k z
  refine ⟨i, QuotientAddGroup.mk' (rationalEquivalences (s.stageSituation i)
    (pullback.snd s.X.hom (s.stageToBase i)) k) w, ?_⟩
  rw [s.stageChowPullback_mk i k w, hw, hz]

/-! ### Eventual injectivity on Chow groups -/

/-- The family of projective lines over `X'` is quasi-compact: `X'` is quasi-compact and the
projection from the family to it is proper. -/
instance compactSpace_projectiveLineProduct_limitBaseChange :
    CompactSpace (projectiveLineProduct (pullback.snd s.X.hom s.limitBaseChange.g)) :=
  QuasiCompact.compactSpace_of_compactSpace
    (pullback.fst (pullback.snd s.X.hom s.limitBaseChange.g)
      (relativeProjectiveLine s.limitBaseChange.baseChange.S ↘
        s.limitBaseChange.baseChange.S))

/-- A cycle rationally equivalent to zero stays rationally equivalent to zero under the
comparison map along a transition, that map descending to the Chow groups. -/
theorem transitionCyclePullback_mem_rationalEquivalences {i j : I} (f : i ⟶ j) (k : ℤ)
    {z : CycleGroup (s.stageSituation j) (pullback.snd s.X.hom (s.stageToBase j)) k}
    (hz : z ∈ rationalEquivalences (s.stageSituation j)
      (pullback.snd s.X.hom (s.stageToBase j)) k) :
    s.transitionCyclePullback f k z ∈ rationalEquivalences (s.stageSituation i)
      (pullback.snd s.X.hom (s.stageToBase i)) k := by
  refine (QuotientAddGroup.eq_zero_iff _).1 ?_
  rw [← QuotientAddGroup.mk'_apply, ← s.transitionChowPullback_mk f k z,
    QuotientAddGroup.mk'_apply, (QuotientAddGroup.eq_zero_iff z).2 hz, map_zero]

/-- **Stacks Project, Tag 0FVQ, descent of a member of a family of projective lines.** An
integral closed subscheme of `X' ×_{S'} 𝐏¹_{S'}` of delta-dimension `k + 1` over `S'` is the
inverse image of an integral closed subscheme of `X_i ×_{S_i} 𝐏¹_{S_i}` of delta-dimension
`k + 1` over `S_i`, for some finite stage `i`. -/
private theorem exists_stage_familyMember (k : ℤ)
    (W : (projectiveLineProduct (pullback.snd s.X.hom s.limitBaseChange.g)).IdealSheafData)
    [IsIntegral W.subscheme]
    (hdim : schemeDeltaDimension s.limitBaseChange.baseChange
      (familyBase (pullback.snd s.X.hom s.limitBaseChange.g) W) = ((k + 1 : ℤ) : EInt)) :
    ∃ (i : I)
      (V : (projectiveLineProduct (pullback.snd s.X.hom (s.stageToBase i))).IdealSheafData),
      IsIntegral V.subscheme ∧
      schemeDeltaDimension (s.stageSituation i)
          (familyBase (pullback.snd s.X.hom (s.stageToBase i)) V) = ((k + 1 : ℤ) : EInt) ∧
      baseChangedFamilyOfSquare (pullback.snd s.X.hom (s.stageToBase i)) (s.limitProjection i)
          (s.isPullback_stageProjection i).w V = W := by
  let e' : projectiveLineProduct (pullback.snd s.X.hom s.limitBaseChange.g) ≅
      pullback s.projectiveLineSystem.X.hom s.projectiveLineSystem.limitBaseChange.g :=
    (isPullback_projectiveLineProductBaseChange s.X.hom s.limitBaseChange.g).isoPullback
  have hsnd' : e'.hom ≫ pullback.snd s.projectiveLineSystem.X.hom
      s.projectiveLineSystem.limitBaseChange.g =
      pullback.fst (pullback.snd s.X.hom s.limitBaseChange.g)
          (relativeProjectiveLine s.limitBaseChange.baseChange.S ↘
            s.limitBaseChange.baseChange.S) ≫ pullback.snd s.X.hom s.limitBaseChange.g :=
    (isPullback_projectiveLineProductBaseChange s.X.hom
      s.limitBaseChange.g).isoPullback_hom_snd
  let Z' : Over (pullback s.projectiveLineSystem.X.hom
      s.projectiveLineSystem.limitBaseChange.g) := Over.mk (W.subschemeι ≫ e'.hom)
  have hclosed' : IsClosedImmersion Z'.hom :=
    inferInstanceAs (IsClosedImmersion (W.subschemeι ≫ e'.hom))
  have hint' : IsIntegral Z'.left := inferInstanceAs (IsIntegral W.subscheme)
  have hlft' : LocallyOfFiniteType (Z'.hom ≫ pullback.snd s.projectiveLineSystem.X.hom
      s.projectiveLineSystem.limitBaseChange.g) :=
    AlgebraicGeometry.locallyOfFiniteType_comp Z'.hom
      (pullback.snd s.projectiveLineSystem.X.hom s.projectiveLineSystem.limitBaseChange.g)
  have hlft2 : @LocallyOfFiniteType Z'.left s.limitBaseChange.baseChange.S
      (Z'.hom ≫ pullback.snd s.projectiveLineSystem.X.hom
        s.projectiveLineSystem.limitBaseChange.g) := hlft'
  have heq : (Z'.hom ≫ pullback.snd s.projectiveLineSystem.X.hom
        s.projectiveLineSystem.limitBaseChange.g :
      Z'.left ⟶ s.limitBaseChange.baseChange.S) =
      familyBase (pullback.snd s.X.hom s.limitBaseChange.g) W := by
    change (W.subschemeι ≫ e'.hom) ≫ pullback.snd s.projectiveLineSystem.X.hom
      s.projectiveLineSystem.limitBaseChange.g = _
    rw [Category.assoc, hsnd']
    rfl
  obtain ⟨i, Zᵢ, hclosedᵢ, hintᵢ, hdimᵢ, ⟨ε⟩⟩ :=
    s.projectiveLineSystem.exists_integral_closedSubscheme_model Z' (k + 1)
      ((schemeDeltaDimension_congr s.limitBaseChange.baseChange heq).trans hdim)
  have hciᵢ : IsClosedImmersion Zᵢ.hom := hclosedᵢ
  have hintegralᵢ : IsIntegral Zᵢ.left := hintᵢ
  let eᵢ : projectiveLineProduct (pullback.snd s.X.hom (s.stageToBase i)) ≅
      pullback s.projectiveLineSystem.X.hom (s.projectiveLineSystem.stageToBase i) :=
    (isPullback_projectiveLineProductBaseChange s.X.hom (s.stageToBase i)).isoPullback
  have hsndᵢ : eᵢ.hom ≫ pullback.snd s.projectiveLineSystem.X.hom
      (s.projectiveLineSystem.stageToBase i) =
      pullback.fst (pullback.snd s.X.hom (s.stageToBase i))
          (relativeProjectiveLine (s.diagram.obj i) ↘ s.diagram.obj i) ≫
        pullback.snd s.X.hom (s.stageToBase i) :=
    (isPullback_projectiveLineProductBaseChange s.X.hom (s.stageToBase i)).isoPullback_hom_snd
  have hlftA : @LocallyOfFiniteType Zᵢ.left (s.diagram.obj i)
      (Zᵢ.hom ≫ pullback.snd s.projectiveLineSystem.X.hom
        (s.projectiveLineSystem.stageToBase i)) :=
    AlgebraicGeometry.locallyOfFiniteType_comp Zᵢ.hom
      (pullback.snd s.projectiveLineSystem.X.hom (s.projectiveLineSystem.stageToBase i))
  have hlftA' : @LocallyOfFiniteType Zᵢ.left (s.stageSituation i).S
      (Zᵢ.hom ≫ pullback.snd s.projectiveLineSystem.X.hom
        (s.projectiveLineSystem.stageToBase i)) := hlftA
  have hlftB : @LocallyOfFiniteType Zᵢ.left (s.diagram.obj i)
      ((Zᵢ.hom ≫ eᵢ.inv).toImage ≫
        familyBase (pullback.snd s.X.hom (s.stageToBase i)) (Zᵢ.hom ≫ eᵢ.inv).ker) :=
    AlgebraicGeometry.locallyOfFiniteType_comp (Zᵢ.hom ≫ eᵢ.inv).toImage
      (familyBase (pullback.snd s.X.hom (s.stageToBase i)) (Zᵢ.hom ≫ eᵢ.inv).ker)
  have hlftB' : @LocallyOfFiniteType Zᵢ.left (s.stageSituation i).S
      ((Zᵢ.hom ≫ eᵢ.inv).toImage ≫
        familyBase (pullback.snd s.X.hom (s.stageToBase i)) (Zᵢ.hom ≫ eᵢ.inv).ker) := hlftB
  have hlftC : @LocallyOfFiniteType Zᵢ.left (s.stageSituation i).S
      ((asIso (Zᵢ.hom ≫ eᵢ.inv).toImage).hom ≫
        familyBase (pullback.snd s.X.hom (s.stageToBase i)) (Zᵢ.hom ≫ eᵢ.inv).ker) := hlftB
  have hdim2 : schemeDeltaDimension (s.stageSituation i)
      (Zᵢ.hom ≫ pullback.snd s.projectiveLineSystem.X.hom
        (s.projectiveLineSystem.stageToBase i)) = ((k + 1 : ℤ) : EInt) := hdimᵢ
  have h1 : (Zᵢ.hom ≫ eᵢ.inv).toImage ≫
      familyBase (pullback.snd s.X.hom (s.stageToBase i)) (Zᵢ.hom ≫ eᵢ.inv).ker =
      (Zᵢ.hom ≫ eᵢ.inv) ≫ (pullback.fst (pullback.snd s.X.hom (s.stageToBase i))
        (relativeProjectiveLine (s.diagram.obj i) ↘ s.diagram.obj i) ≫
        pullback.snd s.X.hom (s.stageToBase i)) := by
    rw [← Category.assoc (Zᵢ.hom ≫ eᵢ.inv).toImage, Scheme.Hom.toImage_imageι]
  have hcomp : Zᵢ.hom ≫ pullback.snd s.projectiveLineSystem.X.hom
        (s.projectiveLineSystem.stageToBase i) =
      (Zᵢ.hom ≫ eᵢ.inv).toImage ≫
        familyBase (pullback.snd s.X.hom (s.stageToBase i)) (Zᵢ.hom ≫ eᵢ.inv).ker := by
    refine Eq.trans (congrArg (fun m ↦ Zᵢ.hom ≫ m)
      (Iso.inv_hom_id_assoc eᵢ (pullback.snd s.projectiveLineSystem.X.hom
        (s.projectiveLineSystem.stageToBase i))).symm) ?_
    refine Eq.trans (Category.assoc Zᵢ.hom eᵢ.inv
      (eᵢ.hom ≫ pullback.snd s.projectiveLineSystem.X.hom
        (s.projectiveLineSystem.stageToBase i))).symm ?_
    exact (congrArg (fun m ↦ (Zᵢ.hom ≫ eᵢ.inv) ≫ m) hsndᵢ).trans h1.symm
  refine ⟨i, (Zᵢ.hom ≫ eᵢ.inv).ker, IsIntegral.of_isIso (Zᵢ.hom ≫ eᵢ.inv).toImage, ?_, ?_⟩
  · exact (schemeDeltaDimension_comp_iso (s.stageSituation i)
      (asIso (Zᵢ.hom ≫ eᵢ.inv).toImage)
      (familyBase (pullback.snd s.X.hom (s.stageToBase i))
        (Zᵢ.hom ≫ eᵢ.inv).ker)).symm.trans
      ((@schemeDeltaDimension_congr (s.stageSituation i) Zᵢ.left _ _ hlftA' hlftB'
        hcomp).symm.trans hdim2)
  · have heSnd : ε.hom.left ≫ pullback.snd Zᵢ.hom (s.projectiveLineSystem.stageProjection i) =
        W.subschemeι ≫ e'.hom := ε.hom.w
    have hsq1 : IsPullback
        (ε.hom.left ≫ pullback.fst Zᵢ.hom (s.projectiveLineSystem.stageProjection i))
        (W.subschemeι ≫ e'.hom) Zᵢ.hom (s.projectiveLineSystem.stageProjection i) := by
      refine IsPullback.of_iso_pullback ⟨?_⟩
        ((Over.forget (pullback s.projectiveLineSystem.X.hom
          s.projectiveLineSystem.limitBaseChange.g)).mapIso ε) rfl heSnd
      calc (ε.hom.left ≫ pullback.fst Zᵢ.hom (s.projectiveLineSystem.stageProjection i)) ≫
            Zᵢ.hom
          = ε.hom.left ≫ (pullback.fst Zᵢ.hom (s.projectiveLineSystem.stageProjection i) ≫
              Zᵢ.hom) := Category.assoc _ _ _
        _ = ε.hom.left ≫ (pullback.snd Zᵢ.hom (s.projectiveLineSystem.stageProjection i) ≫
              s.projectiveLineSystem.stageProjection i) := by rw [pullback.condition]
        _ = (W.subschemeι ≫ e'.hom) ≫ s.projectiveLineSystem.stageProjection i := by
            rw [← Category.assoc, heSnd]
    have hconj : projectiveLineProductMap (pullback.snd s.X.hom (s.stageToBase i))
        (s.limitProjection i) (s.isPullback_stageProjection i).w ≫ eᵢ.hom =
        e'.hom ≫ s.projectiveLineSystem.stageProjection i := s.map_comp_isoPullback i
    have hsq2 : IsPullback W.subschemeι
        (ε.hom.left ≫ pullback.fst Zᵢ.hom (s.projectiveLineSystem.stageProjection i))
        (projectiveLineProductMap (pullback.snd s.X.hom (s.stageToBase i))
          (s.limitProjection i) (s.isPullback_stageProjection i).w)
        (Zᵢ.hom ≫ eᵢ.inv) :=
      hsq1.flip.of_iso' (Iso.refl _) e' (Iso.refl _) eᵢ (Category.id_comp _)
        (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]) hconj.symm
        (by rw [Iso.refl_hom, Category.id_comp, Category.assoc Zᵢ.hom eᵢ.inv eᵢ.hom,
          Iso.inv_hom_id eᵢ, Category.comp_id])
    rw [baseChangedFamilyOfSquare, ker_comap_of_isPullback hsq2,
      Scheme.IdealSheafData.ker_subschemeι]

/-- **Stacks Project, Tag 0FVQ, descent of a basic rational equivalence.** The fibre difference
of an integral closed subscheme of `X' ×_{S'} 𝐏¹_{S'}` of relative dimension `k + 1` at its
generic points and contained in neither distinguished section is the image of a `k`-cycle
rationally equivalent to zero on `X_i`, for some finite stage `i`. -/
private theorem exists_stage_fibreDifference (k : ℤ)
    (W : (projectiveLineProduct (pullback.snd s.X.hom s.limitBaseChange.g)).IdealSheafData)
    [IsIntegral W.subscheme]
    (hdim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension s.limitBaseChange.baseChange.dimensionFunction
        (familyBase (pullback.snd s.X.hom s.limitBaseChange.g) W) ξ.1 = k + 1)
    (h₀ : ¬ Set.range W.subschemeι ⊆
      Set.range (zeroSection (pullback.snd s.X.hom s.limitBaseChange.g)))
    (hInf : ¬ Set.range W.subschemeι ⊆
      Set.range (infinitySection (pullback.snd s.X.hom s.limitBaseChange.g))) :
    ∃ (i : I) (γ : CycleGroup (s.stageSituation i)
      (pullback.snd s.X.hom (s.stageToBase i)) k),
      γ ∈ rationalEquivalences (s.stageSituation i)
        (pullback.snd s.X.hom (s.stageToBase i)) k ∧
      s.stageCyclePullback i k γ = fibreDifference s.limitBaseChange.baseChange
        (pullback.snd s.X.hom s.limitBaseChange.g) k W := by
  obtain ⟨i, V, hintV, hdimV, hcomap⟩ := s.exists_stage_familyMember k W
    (schemeDeltaDimension_familyBase s.limitBaseChange.baseChange
      (pullback.snd s.X.hom s.limitBaseChange.g) W hdim)
  have hVint : IsIntegral V.subscheme := hintV
  have hdimV' : ∀ ξ : genericPoints V.subscheme,
      relativeDimension (s.stageSituation i).dimensionFunction
        (familyBase (pullback.snd s.X.hom (s.stageToBase i)) V) ξ.1 = k + 1 :=
    relativeDimension_familyBase_of_schemeDeltaDimension (s.stageSituation i)
      (pullback.snd s.X.hom (s.stageToBase i)) V hdimV
  have h₀V : ¬ Set.range V.subschemeι ⊆
      Set.range (zeroSection (pullback.snd s.X.hom (s.stageToBase i))) :=
    notSubset_range_constantSection_of_square _ _ _ V integralZeroSection hcomap h₀
  have hInfV : ¬ Set.range V.subschemeι ⊆
      Set.range (infinitySection (pullback.snd s.X.hom (s.stageToBase i))) :=
    notSubset_range_constantSection_of_square _ _ _ V integralInfinitySection hcomap hInf
  refine ⟨i, fibreDifference (s.stageSituation i)
    (pullback.snd s.X.hom (s.stageToBase i)) k V, ?_, ?_⟩
  · exact fibreCycles_rationallyEquivalent (s.stageSituation i)
      (pullback.snd s.X.hom (s.stageToBase i)) k V hdimV' h₀V hInfV
  · rw [s.stageCyclePullback_def i k,
      baseChangeCyclePullbackOfIsPullback_fibreDifference (s.stageToLimitBaseChange i)
        (pullback.snd s.X.hom (s.stageToBase i)) rfl (s.isPullback_stageProjection i) k V
        (schemeDeltaDimension_zeroFiber_le (s.stageSituation i)
          (pullback.snd s.X.hom (s.stageToBase i)) V hdimV' h₀V)
        (schemeDeltaDimension_infinityFiber_le (s.stageSituation i)
          (pullback.snd s.X.hom (s.stageToBase i)) V hdimV' hInfV),
      hcomap]

/-- **Stacks Project, Tag 0FVQ, descent of a rational equivalence.** A `k`-cycle on `X_j` whose
base change to `X'` is rationally equivalent to zero has, at some finite stage `i` under `j`, a
`k`-cycle rationally equivalent to zero with the same base change to `X'`. -/
private theorem exists_stage_rationalEquivalence (j : I) (k : ℤ)
    (z : CycleGroup (s.stageSituation j) (pullback.snd s.X.hom (s.stageToBase j)) k)
    (hz : s.stageCyclePullback j k z ∈ rationalEquivalences s.limitBaseChange.baseChange
      (pullback.snd s.X.hom s.limitBaseChange.g) k) :
    ∃ (i : I) (_ : i ⟶ j) (γ : CycleGroup (s.stageSituation i)
      (pullback.snd s.X.hom (s.stageToBase i)) k),
      γ ∈ rationalEquivalences (s.stageSituation i)
        (pullback.snd s.X.hom (s.stageToBase i)) k ∧
      s.stageCyclePullback i k γ = s.stageCyclePullback j k z := by
  classical
  obtain ⟨J, W, hInt, hDim, h₀, hInf, hLoc, hcoeff⟩ :=
    exists_familyFibreDifferences s.limitBaseChange.baseChange
      (pullback.snd s.X.hom s.limitBaseChange.g) k _ hz
  have hfinite : Finite J :=
    finite_of_locallyFinite_of_nonempty
      (fun l ↦ ((W l).support : Set (projectiveLineProduct
        (pullback.snd s.X.hom s.limitBaseChange.g)))) hLoc
      fun l ↦ have := hInt l; nonempty_support_of_isIntegral (W l)
  have hfintype : Fintype J := Fintype.ofFinite J
  have hstage : ∀ l : J, ∃ (i : I) (γ : CycleGroup (s.stageSituation i)
      (pullback.snd s.X.hom (s.stageToBase i)) k),
      γ ∈ rationalEquivalences (s.stageSituation i)
        (pullback.snd s.X.hom (s.stageToBase i)) k ∧
      s.stageCyclePullback i k γ = fibreDifference s.limitBaseChange.baseChange
        (pullback.snd s.X.hom s.limitBaseChange.g) k (W l) := by
    intro l
    have := hInt l
    exact s.exists_stage_fibreDifference k (W l) (hDim l) (h₀ l) (hInf l)
  choose idx γ₀ hγ₀mem hγ₀ using hstage
  obtain ⟨i, hi⟩ := IsCofiltered.inf_objs_exists (insert j (Finset.image idx Finset.univ))
  have hfj : Nonempty (i ⟶ j) := hi (Finset.mem_insert_self j _)
  have hfl : ∀ l : J, Nonempty (i ⟶ idx l) := fun l ↦
    hi (Finset.mem_insert_of_mem (Finset.mem_image_of_mem idx (Finset.mem_univ l)))
  refine ⟨i, hfj.some, ∑ l : J, s.transitionCyclePullback (hfl l).some k (γ₀ l), ?_, ?_⟩
  · exact AddSubgroup.sum_mem _ fun l _ ↦
      s.transitionCyclePullback_mem_rationalEquivalences (hfl l).some k (hγ₀mem l)
  · have hterm : ∀ l : J, s.stageCyclePullback i k
        (s.transitionCyclePullback (hfl l).some k (γ₀ l)) =
        fibreDifference s.limitBaseChange.baseChange
          (pullback.snd s.X.hom s.limitBaseChange.g) k (W l) := fun l ↦ by
      rw [s.stageCyclePullback_transitionCyclePullback (hfl l).some k (γ₀ l), hγ₀ l]
    rw [map_sum, Finset.sum_congr rfl fun l _ ↦ hterm l]
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x => ?_)
    have hcoe : (∑ l : J, fibreDifference s.limitBaseChange.baseChange
        (pullback.snd s.X.hom s.limitBaseChange.g) k (W l)).1 x =
        ∑ l : J, (fibreDifference s.limitBaseChange.baseChange
          (pullback.snd s.X.hom s.limitBaseChange.g) k (W l)).1 x := by simp
    rw [hcoe, hcoeff x, ← finsum_eq_sum_of_fintype]
    rfl

/-- **Stacks Project, Tag 0FVQ, eventual injectivity for Chow groups.** A `k`-cycle class on
`X_j` whose image in `CH_k(X')` vanishes is annihilated by the comparison homomorphism along
some transition `X_i ⟶ X_j`. -/
@[stacks 0FVQ "Chow groups, eventual injectivity: a k-cycle class on X_j killed by base change
to X' is killed by some transition X_i -> X_j"]
theorem exists_transitionChowPullback_eq_zero (j : I) (k : ℤ)
    (β : chowGroup (s.stageSituation j) (pullback.snd s.X.hom (s.stageToBase j)) k)
    (hβ : s.stageChowPullback j k β = 0) :
    ∃ (i : I) (f : i ⟶ j), s.transitionChowPullback f k β = 0 := by
  obtain ⟨z, hz⟩ := QuotientAddGroup.mk'_surjective
    (rationalEquivalences (s.stageSituation j)
      (pullback.snd s.X.hom (s.stageToBase j)) k) β
  have hmem : s.stageCyclePullback j k z ∈ rationalEquivalences s.limitBaseChange.baseChange
      (pullback.snd s.X.hom s.limitBaseChange.g) k := by
    refine (QuotientAddGroup.eq_zero_iff _).1 ?_
    rw [← QuotientAddGroup.mk'_apply, ← s.stageChowPullback_mk j k z, hz, hβ]
  obtain ⟨i₁, f₁, γ, hγmem, hγ⟩ := s.exists_stage_rationalEquivalence j k z hmem
  have hvanish : s.stageCyclePullback i₁ k (s.transitionCyclePullback f₁ k z - γ) = 0 := by
    rw [map_sub, s.stageCyclePullback_transitionCyclePullback f₁ k z, hγ, sub_self]
  obtain ⟨i₂, f₂, hf₂⟩ := s.exists_transitionCyclePullback_eq_zero i₁ k
    (s.transitionCyclePullback f₁ k z - γ) hvanish
  refine ⟨i₂, f₂ ≫ f₁, ?_⟩
  have heq : s.transitionCyclePullback (f₂ ≫ f₁) k z = s.transitionCyclePullback f₂ k γ := by
    rw [map_sub, sub_eq_zero] at hf₂
    rwa [← s.transitionCyclePullback_comp f₂ f₁ k z]
  rw [← hz, s.transitionChowPullback_mk (f₂ ≫ f₁) k z, heq, QuotientAddGroup.mk'_apply]
  exact (QuotientAddGroup.eq_zero_iff _).2
    (s.transitionCyclePullback_mem_rationalEquivalences f₂ k hγmem)

end FilteredBaseChangeSystem

end Stacks.Chow

end

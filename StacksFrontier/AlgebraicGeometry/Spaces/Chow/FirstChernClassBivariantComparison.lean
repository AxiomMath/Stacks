module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernBivariantClass
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChowOperationsCompatibility
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.FirstChernClassOfRankOne
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.ProperPushforwardChow
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardClosedImmersionSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFirstChernCapCanonical

/-!
# The cap operation of Stacks 0ERM and the Segre-recursion first Chern class

In Situation 0EDT let `X/B` be good and let `ℒ` be an invertible `𝒪_X`-module. This file compares
the cap operation of the bivariant class `f ↦ c₁(f^*ℒ) ∩ -` of Stacks 0ERM
(`AlgebraicGeometry.Space.firstChernBivariantClass`) on a good test space `g : Y' ⟶ X`, which maps
`CH_k(Y')` to `CH_{k-1}(X ×_X Y')` (that is `CH_{k-1}(Y')` along the isomorphism
`X ×_X Y' ⟶ Y'`), with the operation `c₁(g^*ℒ) ∩ -` on `CH_*(Y')` given by the Segre recursion
(`AlgebraicGeometry.Space.PrivateChern.chernCap`).

The proof: for an invertible module the projective bundle has relative dimension `0` and
`𝒪_P(1) = π^*ℒ`, so the Segre-recursion class is the cap product
(`AlgebraicGeometry.Space.PrivateChern.chernCap_one_eq_firstChernCapChow`, on every good space);
and the cap operation of Stacks 0ERM on `Y'` is the cap product with `c₁` of the inverse image of
`ℒ` to `X ×_X Y'`, which the isomorphism `X ×_X Y' ≅ Y'` carries to `c₁(g^*ℒ) ∩ -` on `Y'`
(Stacks 0EQT along that isomorphism).

Stacks 0ES0, stated for the class `AlgebraicGeometry.Space.chernClass` of Definition 0ERZ (the
bivariant class characterized by the relation of Stacks 0ERY) as an equality in `A^1(X)`, is
`AlgebraicGeometry.Space.chernClass_one_eq_firstChernBivariantClass` in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernClassRankOneBivariant`.

## Main results

* `AlgebraicGeometry.Space.chernCap_one_eq_firstChernBivariantClass_cap`: the cap operation of
  Stacks 0ERM is the Segre-recursion operation `AlgebraicGeometry.Space.PrivateChern.chernCap`.
  Stacks 0ES0 itself, for the class `AlgebraicGeometry.Space.chernClass` of Definition 0ERZ, is
  `AlgebraicGeometry.Space.chernClass_one_eq_firstChernBivariantClass`
  (`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernClassRankOneBivariant`).

## References

* [Stacks Project, Tag 0ES0](https://stacks.math.columbia.edu/tag/0ES0)
* [Stacks Project, Tag 0ERM](https://stacks.math.columbia.edu/tag/0ERM)
* [Stacks Project, Tag 0ERY](https://stacks.math.columbia.edu/tag/0ERY)
* [Stacks Project, Tag 0ERZ](https://stacks.math.columbia.edu/tag/0ERZ)
* [Stacks Project, Tag 0EQT](https://stacks.math.columbia.edu/tag/0EQT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open PrivateChern

variable (D : BaseSpaceDimensionSituation.{u}) {X : D.Ambient} (sX : X ⟶ D.space)
    (hX : D.IsGood sX)

/-- The rank-one module `g^*ℒ` on a good test space `g : Y' ⟶ X`, for `ℒ` invertible on `X`. -/
theorem isFiniteLocallyFreeOfRank_one_pullbackLine {Y' : D.Ambient} (g : Y' ⟶ X)
    (hY' : D.IsGood (g ≫ sX)) (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L) :
    PrivateChern.IsFiniteLocallyFreeOfRank D (g ≫ sX) hY'
      (pullbackLine D (g ≫ sX) hY' sX hX g L) 1 :=
  (isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one (Z := goodSpace hY') _).1
    (isInvertibleModule_pullbackLine D (g ≫ sX) hY' sX hX g L hL)

/-- **The cap operation of Stacks 0ERM is the Segre-recursion first Chern class.** In
Situation 0EDT let `X/B` be good and let `ℒ` be an invertible `𝒪_X`-module. On every good test
space `g : Y' ⟶ X`, for every `k` and `α ∈ CH_k(Y')`, the cap operation
`CH_k(Y') ⟶ CH_{k-1}(X ×_X Y')` of the bivariant class of Stacks 0ERM
(`AlgebraicGeometry.Space.firstChernBivariantClass`), followed by the pushforward along the
isomorphism `X ×_X Y' ⟶ Y'`, is `c₁(g^*ℒ) ∩ α` for the operation
`AlgebraicGeometry.Space.PrivateChern.chernCap` on `CH_*(Y') = ⨁_k CH_k(Y')` (defined by the Segre
recursion; `chowGroupCanonicalEquivChowGroup` identifies the Chow groups of Stacks 0EQ6 on which
the bivariant classes act with the summands of `CH_*(Y')`).

This is an auxiliary comparison, not Stacks 0ES0 itself: the equality in `A^1(X)` of the Chern
class `AlgebraicGeometry.Space.chernClass` of Definition 0ERZ (characterized by Stacks 0ERY) with
the class of Lemma 0ERM is `AlgebraicGeometry.Space.chernClass_one_eq_firstChernBivariantClass`
(`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernClassRankOneBivariant`). -/
theorem chernCap_one_eq_firstChernBivariantClass_cap
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    {Y' : D.Ambient} (g : Y' ⟶ X) (hY' : D.IsGood (g ≫ sX))
    (hX' : D.IsGood (pullback.fst (𝟙 X) g ≫ sX)) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY' k) :
    properPushforwardChow.{u, u + 1} D (pullback.fst (𝟙 X) g ≫ sX) hX' (g ≫ sX) hY'
        (pullback.snd (𝟙 X) g) (by rw [← Category.assoc, ← pullback.condition, Category.comp_id])
        (isProper_of_isIso D.site D.base D.base_mem (pullback.snd (𝟙 X) g))
        (DirectSum.of _ (k - 1) (chowGroupCanonicalEquivChowGroup.{u + 1} D _ hX' (k - 1)
          ((firstChernBivariantClass D sX hX L hL).cap g hY' hX' k α))) =
      chernCap.{u, u + 1} (hX := hY') (pullbackLine D (g ≫ sX) hY' sX hX g L) 1
        (isFiniteLocallyFreeOfRank_one_pullbackLine D sX hX g hY' L hL) 1
        (DirectSum.of _ k (chowGroupCanonicalEquivChowGroup.{u + 1} D _ hY' k α)) := by
  obtain ⟨a, rfl⟩ : ∃ a, chowClassCanonical.{u + 1} D (g ≫ sX) hY' k a = α :=
    QuotientAddGroup.mk'_surjective _ α
  have hLY := isInvertibleModule_pullbackLine D (g ≫ sX) hY' sX hX g L hL
  rw [chernCap_one_eq_firstChernCapChow _ _ hLY]
  have hiso := isProper_of_isIso D.site D.base D.base_mem (firstChernBivariantTestIso D g).hom
  have hsnd := isProper_of_isIso D.site D.base D.base_mem (pullback.snd (𝟙 X) g)
  have hsB : pullback.snd (𝟙 X) g ≫ g ≫ sX = pullback.fst (𝟙 X) g ≫ sX := by
    rw [← Category.assoc, ← pullback.condition, Category.comp_id]
  have hk : k = k - 1 + 1 := (Int.sub_add_cancel k 1).symm
  have hcoe : ∀ {l : ℤ} (h : k = l) (x : CycleGroup D (g ≫ sX) k),
      (cycleGroupDegreeCongr D _ h x).1 = x.1 := by
    rintro l rfl x
    rfl
  have hdeg : ∀ {l : ℤ} (h : k = l) (x : CycleGroup D (pullback.fst (𝟙 X) g ≫ sX) k),
      chowGroupCanonicalDegreeCongr D _ hX' h (chowClassCanonical.{u + 1} D _ hX' k x) =
        chowClassCanonical.{u + 1} D _ hX' l (cycleGroupDegreeCongr D _ h x) := by
    rintro l rfl x
    rfl
  have hpushdeg : ∀ {l : ℤ} (h : k = l) (x : CycleGroup D (pullback.fst (𝟙 X) g ≫ sX) k),
      properCyclePushforward D _ hX' (g ≫ sX) hY' hsB hsnd.2.1.2 l
          (cycleGroupDegreeCongr D _ h x) =
        cycleGroupDegreeCongr D _ h
          (properCyclePushforward D _ hX' (g ≫ sX) hY' hsB hsnd.2.1.2 k x) := by
    rintro l rfl x
    rfl
  set y := cycleGroupDegreeCongr D _ hk (properCyclePushforward D (g ≫ sX) hY'
    (pullback.fst (𝟙 X) g ≫ sX) hX' (firstChernBivariantTestIso_hom_comp D sX g) hiso.2.1.2 k a)
    with hy
  -- the cap operation of Stacks 0ERM on the class of `a`
  have hcap : (firstChernBivariantClass D sX hX L hL).cap g hY' hX' k
      (chowClassCanonical.{u + 1} D _ hY' k a) =
      canonicalFirstChernCapCanonical.{u + 1} D (pullback.fst (𝟙 X) g ≫ sX) hX'
        ((modulePullback D.site D.base D.base_mem (firstChernBivariantFst D sX hX g hX')).obj L)
        (modulePullbackInvertible (firstChernBivariantFst D sX hX g hX') L hL) (k - 1) y := by
    change firstChernBivariantCap D sX hX L hL g hY' hX' k _ = _
    rw [firstChernBivariantCap, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
      chowGroupCanonicalProperPushforward_chowClassCanonical, AddEquiv.coe_toAddMonoidHom,
      hdeg]
    rfl
  rw [hcap, chowGroupCanonicalEquivChowGroup_chowClassCanonical,
    of_chowClass_congr D (g ≫ sX) hY' hk a (cycleGroupDegreeCongr D _ hk a)
      (hcoe hk a).symm]
  refine Eq.trans ?_ (firstChernCapChow_of_chowClass D (g ≫ sX) hY' _ hLY (k - 1) _).symm
  rw [canonicalFirstChernCapCanonical, AddMonoidHom.comp_apply,
    chowGroupCanonicalEquivChowGroup_chowClassCanonical, properPushforwardChow_of,
    chowGroupProperPushforward_chowClass]
  refine congrArg (DirectSum.of (fun k => chowGroup.{u + 1} D (g ≫ sX) hY' k) (k - 1))
    (chowClass_eq_of_chowClassCanonical_eq D (g ≫ sX) hY' ?_)
  let q : (⟨pullback (𝟙 X) g, hX'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
      ⟨Y', hY'.1⟩ := ObjectProperty.homMk (pullback.snd (𝟙 X) g)
  let gY : (⟨Y', hY'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hX.1⟩ :=
    ObjectProperty.homMk g
  have hcomp : q ≫ gY = firstChernBivariantFst D sX hX g hX' :=
    ObjectProperty.hom_ext _ (pullback.condition.symm.trans (Category.comp_id _))
  have e : (modulePullback D.site D.base D.base_mem q).obj
        (pullbackLine D (g ≫ sX) hY' sX hX g L) ≅
      (modulePullback D.site D.base D.base_mem (firstChernBivariantFst D sX hX g hX')).obj L :=
    (modulePullbackCompIso D.site D.base D.base_mem q gY).app L ≪≫ eqToIso (by rw [hcomp])
  have hc := canonicalFirstChernCapCanonical_congr_iso hX' _ _
    (modulePullbackInvertible q _ hLY)
    (modulePullbackInvertible (firstChernBivariantFst D sX hX g hX') L hL) e (k - 1) y
  rw [canonicalFirstChernCapCanonical, canonicalFirstChernCapCanonical, AddMonoidHom.comp_apply,
    AddMonoidHom.comp_apply] at hc
  -- Stacks 0EQT along `q`
  have h0EQT := chowClassCanonical_properPushforward_canonicalFirstChernCap_of_component D hX' hY'
    q hsB hsnd _ hLY (k - 1) (fun β hβ =>
      isRationallyEquivalentToZeroCanonical_properCyclePushforward D _ hX' _ hY' hsB hsnd (k - 1)
        β hβ) y
  have hpush : properCyclePushforward D (pullback.fst (𝟙 X) g ≫ sX) hX' (g ≫ sX) hY' hsB
      hsnd.2.1.2 (k - 1 + 1) y = cycleGroupDegreeCongr D _ hk a := by
    rw [hy, hpushdeg, properCyclePushforward_comp D _ _ _
      hY' hX' hY' (firstChernBivariantTestIso_hom_comp D sX g) hsB hiso hsnd k]
    congr 1
    rw [properCyclePushforward_congr D (g ≫ sX) hY' (g ≫ sX) hY'
      (show (firstChernBivariantTestIso D g).hom ≫ pullback.snd (𝟙 X) g = 𝟙 Y' by
        simp [firstChernBivariantTestIso]) _ _ (Category.id_comp _)
      (isQuasiCompact_of_isIso D.site D.base D.base_mem (𝟙 Y')) k a]
    exact properCyclePushforward_id D (g ≫ sX) hY' _ k a
  have h1 := congrArg (chowGroupCanonicalProperPushforward.{u + 1} D _ hX' _ hY' hsB hsnd
    (k - 1)) hc
  rw [chowGroupCanonicalProperPushforward_chowClassCanonical,
    chowGroupCanonicalProperPushforward_chowClassCanonical] at h1
  rw [← h1, h0EQT, hpush]
  rfl

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FiniteLocallyFreePushPull
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FiniteLocallyFreePushPullUnranked
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackAssociatedCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackOfCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardModuleCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankGeometricLength
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffineBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# Push and pull along a finite locally free morphism, at the constructed flat pullback

In Situation 0EDT let `X/B` and `Y/B` be good and let `f : X ⟶ Y` be finite locally free of
degree `d` in the sense of Stacks 03ZV. The third conclusion of **Stacks 0EPE** is the identity
`f_*f^*α = dα` on `Z_k(Y)`, and
`AlgebraicGeometry.Space.properPushforward_flatCyclePullback` proves it for an arbitrary
inhabitant `pb` of `AlgebraicGeometry.Space.FlatCyclePullback`, that is for arbitrary
multiplicities satisfying the formula that defines the flat pullback.

Quantifying over `pb` is a generalization of the statement, but the conclusion it reaches is
then not a statement about the flat pullback of Stacks 0EP8: the multiplicities of an arbitrary
`pb` are not tied to the scheme-theoretic inverse image. This file instantiates `pb` at the
constructed flat pullback `AlgebraicGeometry.Space.flatCyclePullback`, whose two hypotheses —
flatness and relative dimension `0` — are exactly the second conclusion of Stacks 0EPE and so need
not be assumed. The resulting statement is about `f^*` itself.

## Main definitions

* `AlgebraicGeometry.Space.finiteLocallyFreeCyclePullback`: the flat pullback of cycles of
  Stacks 0EP8 along a finite locally free morphism of degree `d`, with its flatness and
  relative-dimension hypotheses discharged from the morphism.

## Main results

* `AlgebraicGeometry.Space.isFlat_hom_of_isFiniteLocallyFreeOfRank` and
  `AlgebraicGeometry.Space.hasRelativeDimension_zero_of_isFiniteLocallyFreeOfRank`: the two
  conjuncts of the second conclusion of Stacks 0EPE.
* `AlgebraicGeometry.Space.isQuasiCompact_hom_of_isFiniteLocallyFreeOfRank`: quasi-compactness,
  the part of the first conclusion of Stacks 0EPE that the proper pushforward of Stacks 0EP1
  asks for.
* `AlgebraicGeometry.Space.finiteLocallyFreeCyclePullback_mult`: the multiplicity of the
  constructed flat pullback is the coefficient of the cycle `[f^{-1}(W)]` of the
  scheme-theoretic inverse image.
* `AlgebraicGeometry.Space.properPushforward_finiteLocallyFreeCyclePullback`: the third
  conclusion of Stacks 0EPE for the flat pullback of Stacks 0EP8 itself, granted the degree
  computation `hdeg`.
* `AlgebraicGeometry.Space.finsum_finiteLocallyFreeCyclePullback_mult_mul_cycleResidueDegree_eq`:
  that degree computation, **proved**.
* `AlgebraicGeometry.Space.properPushforward_finiteLocallyFreeCyclePullback_eq_zsmul`: the third
  conclusion of **Stacks 0EPE**, unconditionally.

Along the way:

* `geometricLength_pushforwardStructureModule_eq_of_isPullback_of_mem_genericPoints`: the direct
  image of the structure sheaf of a base change of a finite locally free morphism of
  degree `d` has length `d` at a geometric point over a generic point of an integral base.
* `AlgebraicGeometry.Space.geometricLength_closedSubspaceDirectImageStructureSheaf_preimage_eq`:
  the same read on `f^{-1}(W)` for an integral closed subspace `W ⊆ Y`.
* `AlgebraicGeometry.Space.properPushforwardCoeff_eq_properCyclePushforwardCoeff` and
  `AlgebraicGeometry.Space.properCycleDegree_eq_properPushforwardWeight`: the two forms of the
  pushforward coefficient of Stacks 0EP1 agree.

## Implementation notes

**How `hdeg` is proved.** The hypothesis is the degree of the fibre of `f` over the generic
point `η` of an integral closed subspace `W ⊆ Y` of δ-dimension `k`: the sum, over the integral
closed subspaces of `X` whose integral closed image is `W`, of the multiplicity in `f^{-1}(W)`
times the degree of the residue field extension there. Where the multiplicity does not vanish
the δ-dimension is preserved, so the residue degree is the weight of Stacks 0EP0, and the sum is
the coefficient of `W` in the proper pushforward of Stacks 0EP1 of the cycle `[f^{-1}(W)]_k`.
Part (1) of Stacks 0EP3,
`AlgebraicGeometry.Space.properCyclePushforwardCoeff_closedSubspaceCycle_eq`, identifies that
coefficient with the length of `f_*𝒪_{f^{-1}(W)}` at `η`. So no reindexing of the fibre sum of
`AlgebraicGeometry.Space.geometricLength_directImageModule_toNat_eq_finsum` from the points of
`X` over `η` to the integral closed subspaces over `W` is needed: that reindexing is what the
proof of Stacks 0EP3 already performs, by
`AlgebraicGeometry.Space.bijOn_ambientGenericPoint_moduleSupport_fibre`.

The pushforward coefficient has two forms — a sum over the fibre
weighted by `AlgebraicGeometry.Space.properPushforwardWeight`
(`AlgebraicGeometry.Space.properPushforwardCoeff`, which is what the third conclusion above is
stated with) and a sum over all integral closed subspaces weighted by
`AlgebraicGeometry.Space.properCycleMult`
(`AlgebraicGeometry.Space.properCyclePushforwardCoeff`, which Stacks 0EP3 is stated with). They
agree: the multiplicity is the indicator of the fibre times the weight, the degree of
Stacks 0EP1 and the weight of Stacks 0EP0 being the same function by `rfl`.

**The length `d` at the generic point of `W`.** The direct image `f_*𝒪_{f^{-1}(W)}` is formed
along `f^{-1}(W) → X → Y`, and the square `f^{-1}(W) → W, X → Y` is cartesian —
`CategoryTheory.Subfunctor.isPullback_preimage` is Stacks 083Q for the scheme-theoretic inverse
image — so that composite is `f^{-1}(W) → W → Y` and the length is unchanged along the closed
immersion `W ⟶ Y` by Stacks 0EE3. On `W` the module is `(f_W)_*𝒪_{f^{-1}(W)}`, which the
base-change clause of Stacks 07U8 at the structure sheaf
(`AlgebraicGeometry.Space.modulePullbackPushforwardUnitIso`, available for an arbitrary base
change of an affine morphism) identifies with `i^*(f_*𝒪_X)`. Its length there is `d` by
`geometricLength_modulePullback_pushforwardStructureModule_eq_of_mem_genericPoints`: the rank of
a quasi-coherent module survives an arbitrary pullback
(`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_modulePullback_of_isQuasicoherentOnSite`,
the rank clause of Stacks 0409), and a module of rank `d` has length `d` at a geometric point
whose étale local ring is a field, which it is over a generic point of the integral `W` by
Stacks 0AD4.

**The first two conclusions.** None of properness, flatness, relative dimension `0` or
quasi-compactness uses the rank. They are read off the *unranked* definition of Stacks 03ZV,
after forgetting the rank by
`AlgebraicGeometry.Space.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree`, so the only hypotheses
below are Situation 0EDT, goodness, and finite local freeness of degree `d` itself.

## References

* [Stacks Project, Tag 0EPE](https://stacks.math.columbia.edu/tag/0EPE)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
* [Stacks Project, Tag 03ZU](https://stacks.math.columbia.edu/tag/03ZU)
* [Stacks Project, Tag 03ZV](https://stacks.math.columbia.edu/tag/03ZV)
* [Stacks Project, Tag 03ZW](https://stacks.math.columbia.edu/tag/03ZW)
* [Stacks Project, Tag 0416](https://stacks.math.columbia.edu/tag/0416)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 0AD4](https://stacks.math.columbia.edu/tag/0AD4)
* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE3](https://stacks.math.columbia.edu/tag/0EE3)
* [Stacks Project, Tag 0EP0](https://stacks.math.columbia.edu/tag/0EP0)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EP3](https://stacks.math.columbia.edu/tag/0EP3)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section ConstructedPullback

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : AlgebraicSpaces D.site D.base D.base_mem}

/-- A finite locally free morphism of degree `d` is flat: the first conjunct of the second
conclusion of Stacks 0EPE. -/
theorem isFlat_hom_of_isFiniteLocallyFreeOfRank (f : X ⟶ Y) (d : ℕ)
    (hf : IsFiniteLocallyFreeOfRank D.site D.base D.base_mem f d) :
    IsFlat D.site D.base D.base_mem f.hom :=
  (isFlat_and_hasRelativeDimension_zero_of_isFiniteLocallyFree D.site D.base D.base_mem f
    (IsFiniteLocallyFreeOfRank.isFiniteLocallyFree D.site D.base D.base_mem hf)).1

/-- A finite locally free morphism of degree `d` has relative dimension `0`: the last conjunct
of the second conclusion of Stacks 0EPE. -/
theorem hasRelativeDimension_zero_of_isFiniteLocallyFreeOfRank (f : X ⟶ Y) (d : ℕ)
    (hf : IsFiniteLocallyFreeOfRank D.site D.base D.base_mem f d) :
    HasRelativeDimension 0 D.site D.base D.base_mem f.hom :=
  (isFlat_and_hasRelativeDimension_zero_of_isFiniteLocallyFree D.site D.base D.base_mem f
    (IsFiniteLocallyFreeOfRank.isFiniteLocallyFree D.site D.base D.base_mem hf)).2.2

/-- A finite locally free morphism of degree `d` is quasi-compact. -/
theorem isQuasiCompact_hom_of_isFiniteLocallyFreeOfRank (f : X ⟶ Y) (d : ℕ)
    (hf : IsFiniteLocallyFreeOfRank D.site D.base D.base_mem f d) :
    IsQuasiCompact D.site D.base D.base_mem f.hom :=
  isQuasiCompact_of_isFiniteLocallyFree D.site D.base D.base_mem f
    (IsFiniteLocallyFreeOfRank.isFiniteLocallyFree D.site D.base D.base_mem hf)

/-- **The flat pullback of cycles along a finite locally free morphism of degree `d`.** This is
the flat pullback of Stacks 0EP8, `AlgebraicGeometry.Space.flatCyclePullback`, whose two
hypotheses are discharged by the second conclusion of Stacks 0EPE: a finite locally free
morphism is flat of relative dimension `0`. -/
def finiteLocallyFreeCyclePullback (sX : X.obj ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y.obj ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y) (hbase : f.hom ≫ sY = sX) (d : ℕ)
    (hf : IsFiniteLocallyFreeOfRank D.site D.base D.base_mem f d) :
    FlatCyclePullback D sX hX sY hY f.hom 0 :=
  flatCyclePullback D sX hX sY hY f.hom hbase 0
    (isFlat_hom_of_isFiniteLocallyFreeOfRank D f d hf)
    (hasRelativeDimension_zero_of_isFiniteLocallyFreeOfRank D f d hf)

/-- The multiplicity of the flat pullback along a finite locally free morphism of degree `d` at
an integral closed subspace `T ⊆ X` is the coefficient of `T` in the cycle `[f^{-1}(W)]` of the
scheme-theoretic inverse image, which is part (1) of Stacks 0EP8. -/
@[simp]
theorem finiteLocallyFreeCyclePullback_mult (sX : X.obj ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y.obj ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y) (hbase : f.hom ≫ sY = sX) (d : ℕ)
    (hf : IsFiniteLocallyFreeOfRank D.site D.base D.base_mem f d)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y.obj)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X.obj) :
    (finiteLocallyFreeCyclePullback D sX hX sY hY f hbase d hf).mult W T =
      (flatPullbackIntegralCycle D sX hX sY hY f.hom hbase 0
        (isFlat_hom_of_isFiniteLocallyFreeOfRank D f d hf)
        (hasRelativeDimension_zero_of_isFiniteLocallyFreeOfRank D f d hf) W).1 T :=
  rfl

/-- **Stacks 0EPE, third conclusion, for the flat pullback of Stacks 0EP8 itself.** In
Situation 0EDT let `X/B` and `Y/B` be good and let `f : X ⟶ Y` be finite locally free of
degree `d`. Then `f_*f^*α = dα` for every `α ∈ Z_k(Y)`, with `f^*` the constructed flat pullback
`AlgebraicGeometry.Space.finiteLocallyFreeCyclePullback` and `f_*` the proper pushforward of
Stacks 0EP1, whose quasi-compactness hypothesis is supplied by the first conclusion of
Stacks 0EPE, granted that the degree of the fibre of `f` over the generic point of every integral
closed subspace of `Y` of δ-dimension `k` is `d` (`hdeg`). -/
theorem properPushforward_finiteLocallyFreeCyclePullback (sX : X.obj ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y.obj ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y)
    (hbase : f.hom ≫ sY = sX) (d : ℕ)
    (hf : IsFiniteLocallyFreeOfRank D.site D.base D.base_mem f d) (k : ℤ)
    (hdeg : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem Y.obj,
      deltaDimension D sY W = k →
      ∑ᶠ T ∈ {T : IntegralClosedSubspace D.site D.base D.base_mem X.obj |
          cycleImageSubspace D sY hY f.hom T = W},
        (finiteLocallyFreeCyclePullback D sX hX sY hY f hbase d hf).mult W T *
          (cycleResidueDegree D sX hX sY hY f.hom
            (T.ambientGenericPoint D.site D.base D.base_mem) : ℤ) = (d : ℤ))
    (α : CycleGroup D sY k) :
    properPushforward D sX hX sY hY hbase
        (isQuasiCompact_hom_of_isFiniteLocallyFreeOfRank D f d hf) k
        ((finiteLocallyFreeCyclePullback D sX hX sY hY f hbase d hf).map k k (by simp) α) =
      (d : ℤ) • α :=
  properPushforward_flatCyclePullback_of_isFiniteLocallyFree D sX hX sY hY f hbase d
    (IsFiniteLocallyFreeOfRank.isFiniteLocallyFree D.site D.base D.base_mem hf)
    (finiteLocallyFreeCyclePullback D sX hX sY hY f hbase d hf) k hdeg α

end ConstructedPullback

/-! ### The direct image of the structure sheaf of a base change -/

section BaseChangeLength

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y X' W : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : W ⟶ Y} {f' : X' ⟶ W} {g' : X' ⟶ X}

/-- **`(f')_*𝒪_{X'}` has length `d` at a geometric point of `W` over a generic point**, for a
cartesian square

```
X' --g'--> X
|f'         |f
v           v
W  --g-->   Y
```

with `W` integral and `f` finite locally free of degree `d` in the sense of Stacks 03ZV. -/
theorem geometricLength_pushforwardStructureModule_eq_of_isPullback_of_mem_genericPoints
    (sq : IsPullback g' f' f g) (d : ℕ) (hf : IsFiniteLocallyFreeOfRank B S hS f d)
    (hint : IsIntegralSpace B S hS W.1) (wbar : GeometricPoint B S hS W.1)
    (hgen : wbar.image ∈ genericPoints (points B S hS W.1)) :
    geometricLength B S hS W wbar (pushforwardStructureModule B S hS f') = d :=
  (geometricLength_eq_of_iso B S hS W wbar
      (modulePullbackPushforwardUnitIso sq hf.1.1).symm).trans
    (geometricLength_modulePullback_pushforwardStructureModule_eq_of_mem_genericPoints
      B S hS X f d hf g hint wbar hgen)

end BaseChangeLength

/-! ### The two spellings of the pushforward coefficient of Stacks 0EP1 -/

section CoeffBridge

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y)

/-- **The degree of Stacks 0EP1 and the weight of Stacks 0EP0 are the same function.** Both are
the residue degree at the generic point of `Z` when the δ-dimension of the integral closed image
is that of `Z`, and zero otherwise. -/
theorem properCycleDegree_eq_properPushforwardWeight
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    properCycleDegree D sX hX sY hY f Z = properPushforwardWeight D sX hX sY hY f Z :=
  rfl

/-- **The two spellings of the pushforward coefficient of Stacks 0EP1 agree.** The sum over the
integral closed subspaces with integral closed image `W`, weighted by
`AlgebraicGeometry.Space.properPushforwardWeight`
(`AlgebraicGeometry.Space.properPushforwardCoeff`), and the sum over *all* integral closed
subspaces, weighted by `AlgebraicGeometry.Space.properCycleMult`
(`AlgebraicGeometry.Space.properCyclePushforwardCoeff`), are the same integer. -/
theorem properPushforwardCoeff_eq_properCyclePushforwardCoeff
    (α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    properPushforwardCoeff D sX hX sY hY f α W =
      properCyclePushforwardCoeff D sX hX sY hY f α W := by
  classical
  rw [properPushforwardCoeff, finsum_mem_def, properCyclePushforwardCoeff]
  refine finsum_congr fun Z => ?_
  simp only [Set.indicator_apply, properCycleMult, Set.mem_ofPred_eq]
  split_ifs
  · rfl
  · rw [mul_zero]

end CoeffBridge

/-! ### The degree of the fibre over the generic point of an integral closed subspace -/

section Degree

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : AlgebraicSpaces D.site D.base D.base_mem}

/-- **`f_*𝒪_{f^{-1}(W)}` has length `d` at a geometric point over the generic point of `W`.** In
Situation 0EDT let `X/B` and `Y/B` be good, let `f : X ⟶ Y` be finite locally free of degree `d`
and let `W ⊆ Y` be an integral closed subspace with closed immersion `i : W ⟶ Y`. Then the
direct image along `f^{-1}(W) → X → Y` of the structure sheaf of the scheme-theoretic inverse
image has length `d` at every geometric point of `Y` of the form `i(w̄)` with `w̄` over the
generic point of `W`. -/
theorem geometricLength_closedSubspaceDirectImageStructureSheaf_preimage_eq
    (sX : X.obj ⟶ D.space) (hX : D.IsGood sX) (sY : Y.obj ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (d : ℕ) (hf : IsFiniteLocallyFreeOfRank D.site D.base D.base_mem f d)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y.obj)
    (wbar : GeometricPoint D.site D.base D.base_mem W.subspace.toFunctor)
    (hwbar : wbar.image = W.genericPoint D.site D.base D.base_mem) :
    geometricLength D.site D.base D.base_mem ⟨Y.obj, hY.1⟩
        (geometricPointMap W.subspace.ι wbar)
        (closedSubspaceDirectImageStructureSheaf D sX hX sY hY f.hom
          (W.subspace.preimage f.hom)
          (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f.hom W)) = d := by
  have hZ : IsClosedSubspace D.site D.base D.base_mem (W.subspace.preimage f.hom) :=
    isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f.hom W
  set i : (⟨W.subspace.toFunctor, W.isClosedSubspace.1⟩ :
      AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y.obj, hY.1⟩ :=
    ObjectProperty.homMk W.subspace.ι
  set j : (⟨(W.subspace.preimage f.hom).toFunctor, hZ.1⟩ :
      AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X.obj, hX.1⟩ :=
    ObjectProperty.homMk (W.subspace.preimage f.hom).ι
  set fA : (⟨X.obj, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y.obj, hY.1⟩ :=
    ObjectProperty.homMk f.hom
  set fW : (⟨(W.subspace.preimage f.hom).toFunctor, hZ.1⟩ :
      AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨W.subspace.toFunctor, W.isClosedSubspace.1⟩ :=
    ObjectProperty.homMk (W.subspace.fromPreimage f.hom)
  have hpb : IsPullback fW j i fA :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun T : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace D.site D.base D.base_mem T))
      (Subfunctor.isPullback_preimage f.hom W.subspace)
  have hsq : IsPullback j fW fA i := hpb.flip
  have hG : closedSubspaceDirectImageStructureSheaf D sX hX sY hY f.hom
      (W.subspace.preimage f.hom) hZ =
      pushforwardStructureModule D.site D.base D.base_mem (j ≫ fA) := rfl
  rw [hG, hsq.w,
    geometricLength_eq_of_iso D.site D.base D.base_mem ⟨Y.obj, hY.1⟩ _
      (((modulePushforwardCompIso D.site D.base D.base_mem fW i).app
        (SheafOfModules.unit _)).symm),
    Functor.comp_obj]
  exact (geometricLength_modulePushforward_of_isClosedImmersion D.site D.base D.base_mem i
      W.isClosedSubspace.2 wbar _).trans
    (geometricLength_pushforwardStructureModule_eq_of_isPullback_of_mem_genericPoints
      D.site D.base D.base_mem hsq d hf W.isIntegralSpace wbar
      (by rw [hwbar]; exact W.genericPoint_mem_genericPoints D))

/-- **The degree of the fibre of a finite locally free morphism of degree `d` over the generic
point of an integral closed subspace is `d`.** In Situation 0EDT let `X/B` and `Y/B` be good, let
`f : X ⟶ Y` be finite locally free of degree `d` and let `W ⊆ Y` be an integral closed subspace
of δ-dimension `k`. Then

`∑_{T : f(T)^- = W} mult_T(f^{-1}(W)) · [R(T) : R(W)] = d`,

the sum over the integral closed subspaces of `X` with integral closed image `W`. -/
theorem finsum_finiteLocallyFreeCyclePullback_mult_mul_cycleResidueDegree_eq
    (sX : X.obj ⟶ D.space) (hX : D.IsGood sX) (sY : Y.obj ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f.hom ≫ sY = sX) (d : ℕ)
    (hf : IsFiniteLocallyFreeOfRank D.site D.base D.base_mem f d)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y.obj) :
    ∑ᶠ T ∈ {T : IntegralClosedSubspace D.site D.base D.base_mem X.obj |
        cycleImageSubspace D sY hY f.hom T = W},
      (finiteLocallyFreeCyclePullback D sX hX sY hY f hbase d hf).mult W T *
        (cycleResidueDegree D sX hX sY hY f.hom
          (T.ambientGenericPoint D.site D.base D.base_mem) : ℤ) = (d : ℤ) := by
  classical
  have hZ : IsClosedSubspace D.site D.base D.base_mem (W.subspace.preimage f.hom) :=
    isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f.hom W
  have hdim : deltaDimensionSubspace D sX hX (W.subspace.preimage f.hom) hZ ≤
      ((deltaDimension D sY W + ((0 : ℕ) : ℤ) : ℤ) : EInt) :=
    deltaDimensionSubspace_preimage_integralClosedSubspace_le D sX hX sY hY f.hom hbase 0
      (isFlat_hom_of_isFiniteLocallyFreeOfRank D f d hf)
      (hasRelativeDimension_zero_of_isFiniteLocallyFreeOfRank D f d hf) W
  have hwbarim : (canonicalGeometricPoint D.site D.base D.base_mem W.subspace.toFunctor
      (W.genericPoint D.site D.base D.base_mem)).image =
      W.genericPoint D.site D.base D.base_mem :=
    canonicalGeometricPoint_image D.site D.base D.base_mem _ _
  have hybarim : (geometricPointMap W.subspace.ι
      (canonicalGeometricPoint D.site D.base D.base_mem W.subspace.toFunctor
        (W.genericPoint D.site D.base D.base_mem))).image =
      W.ambientGenericPoint D.site D.base D.base_mem := by
    rw [geometricPointMap_image, hwbarim]
    rfl
  have hγY : ∀ y, (Function.update
      (canonicalGeometricPoint D.site D.base D.base_mem Y.obj)
      (W.ambientGenericPoint D.site D.base D.base_mem)
      (geometricPointMap W.subspace.ι
        (canonicalGeometricPoint D.site D.base D.base_mem W.subspace.toFunctor
          (W.genericPoint D.site D.base D.base_mem))) y).LiesOver y := by
    intro y
    by_cases h : y = W.ambientGenericPoint D.site D.base D.base_mem
    · subst h
      rw [Function.update_self]
      exact hybarim
    · rw [Function.update_of_ne h]
      exact canonicalGeometricPoint_image D.site D.base D.base_mem _ _
  calc ∑ᶠ T ∈ {T : IntegralClosedSubspace D.site D.base D.base_mem X.obj |
        cycleImageSubspace D sY hY f.hom T = W},
        (finiteLocallyFreeCyclePullback D sX hX sY hY f hbase d hf).mult W T *
          (cycleResidueDegree D sX hX sY hY f.hom
            (T.ambientGenericPoint D.site D.base D.base_mem) : ℤ)
      = ∑ᶠ T ∈ {T : IntegralClosedSubspace D.site D.base D.base_mem X.obj |
          cycleImageSubspace D sY hY f.hom T = W},
          (closedSubspaceCycle D sX hX (W.subspace.preimage f.hom) hZ
              (deltaDimension D sY W + ((0 : ℕ) : ℤ)) hdim).1 T *
            properPushforwardWeight D sX hX sY hY f.hom T := by
        refine finsum_mem_congr rfl fun T hT => ?_
        have hco : (finiteLocallyFreeCyclePullback D sX hX sY hY f hbase d hf).mult W T =
            (closedSubspaceCycle D sX hX (W.subspace.preimage f.hom) hZ
              (deltaDimension D sY W + ((0 : ℕ) : ℤ)) hdim).1 T := rfl
        rw [← hco]
        by_cases hz : (finiteLocallyFreeCyclePullback D sX hX sY hY f hbase d hf).mult W T = 0
        · rw [hz, zero_mul, zero_mul]
        · have h1 : deltaDimension D sX T = deltaDimension D sY W := by
            simpa using (finiteLocallyFreeCyclePullback D sX hX sY hY f hbase d
              hf).deltaDimension_eq_of_mult_ne_zero W T hz
          rw [properPushforwardWeight_eq_cycleResidueDegree D sX hX sY hY f.hom
            (by rw [hT, h1] : deltaDimension D sY (cycleImageSubspace D sY hY f.hom T) =
              deltaDimension D sX T)]
    _ = properPushforwardCoeff D sX hX sY hY f.hom
          (closedSubspaceCycle D sX hX (W.subspace.preimage f.hom) hZ
            (deltaDimension D sY W + ((0 : ℕ) : ℤ)) hdim).1 W := rfl
    _ = properCyclePushforwardCoeff D sX hX sY hY f.hom
          (closedSubspaceCycle D sX hX (W.subspace.preimage f.hom) hZ
            (deltaDimension D sY W + ((0 : ℕ) : ℤ)) hdim).1 W :=
        properPushforwardCoeff_eq_properCyclePushforwardCoeff D sX hX sY hY f.hom _ W
    _ = cycleCoeffOfModule D sY hY
          (closedSubspaceDirectImageStructureSheaf D sX hX sY hY f.hom
            (W.subspace.preimage f.hom) hZ) (deltaDimension D sY W + ((0 : ℕ) : ℤ))
          (Function.update (canonicalGeometricPoint D.site D.base D.base_mem Y.obj)
            (W.ambientGenericPoint D.site D.base D.base_mem)
            (geometricPointMap W.subspace.ι
              (canonicalGeometricPoint D.site D.base D.base_mem W.subspace.toFunctor
                (W.genericPoint D.site D.base D.base_mem)))) W :=
        congrFun (properCyclePushforwardCoeff_closedSubspaceCycle_eq D sX hX sY hY hbase
          (isProper_of_isFiniteLocallyFree D.site D.base D.base_mem f
            (IsFiniteLocallyFreeOfRank.isFiniteLocallyFree D.site D.base D.base_mem hf))
          (W.subspace.preimage f.hom) hZ (deltaDimension D sY W + ((0 : ℕ) : ℤ)) hdim _ hγY) W
    _ = (d : ℤ) := by
        rw [cycleCoeffOfModule, if_pos (by simp), Function.update_self,
          geometricLength_closedSubspaceDirectImageStructureSheaf_preimage_eq D sX hX sY hY f d hf
            W _ hwbarim]
        simp

/-- In Situation 0EDT let `X/B` and `Y/B` be good and let
`f : X ⟶ Y` be finite locally free of degree `d`. Then

`f_*f^*α = dα`

for every `α ∈ Z_k(Y)`, with `f^*` the flat pullback of Stacks 0EP8
(`AlgebraicGeometry.Space.finiteLocallyFreeCyclePullback`, whose flatness and
relative-dimension hypotheses are the second conclusion of Stacks 0EPE) and `f_*` the proper
pushforward of Stacks 0EP1 (whose quasi-compactness hypothesis is the first conclusion). -/
@[stacks 0EPE "f_* f^* alpha = d alpha"]
theorem properPushforward_finiteLocallyFreeCyclePullback_eq_zsmul
    (sX : X.obj ⟶ D.space) (hX : D.IsGood sX) (sY : Y.obj ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f.hom ≫ sY = sX) (d : ℕ)
    (hf : IsFiniteLocallyFreeOfRank D.site D.base D.base_mem f d) (k : ℤ)
    (α : CycleGroup D sY k) :
    properPushforward D sX hX sY hY hbase
        (isQuasiCompact_hom_of_isFiniteLocallyFreeOfRank D f d hf) k
        ((finiteLocallyFreeCyclePullback D sX hX sY hY f hbase d hf).map k k (by simp) α) =
      (d : ℤ) • α :=
  properPushforward_finiteLocallyFreeCyclePullback D sX hX sY hY f hbase d hf k
    (fun W _ => finsum_finiteLocallyFreeCyclePullback_mult_mul_cycleResidueDegree_eq D sX hX sY hY
      f hbase d hf W) α

end Degree

end AlgebraicGeometry.Space

end

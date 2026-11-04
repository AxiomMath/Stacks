module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.RegularImmersionGysinComposition
public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysin
public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionProductRegularImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.Components
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.SmoothConnectedComponents
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Motives.ChowGroups

/-!
# The action of correspondences on rational Chow groups, and their composition

Let `X` and `Y` be schemes over a field `k` which are smooth and proper, equidimensional of
dimensions `d` and `e`. Section 0FFZ of the Stacks Project defines, for a correspondence
`c ∈ Corrʳ(X, Y) = CH^{d + r}(X × Y) ⊗ ℚ`, its pushforward action on rational Chow groups

  `c_*(α) = pr₂,*(c · pr₁^* α) ∈ CH^{i + r}(Y) ⊗ ℚ`   for `α ∈ CH^i(X) ⊗ ℚ`,

and, for a third such scheme `Z` of dimension `f`, the composition of correspondences

  `c' ∘ c = pr₁₃,*(pr₁₂^* c · pr₂₃^* c') ∈ Corr^{r + s}(X, Z)`
  for `c ∈ Corrʳ(X, Y)` and `c' ∈ Corrˢ(Y, Z)`.

This file constructs both operations out of the three operations of Chapter 42 they are made
of: flat pullback along the projections, the intersection product of Stacks 0FC0 on the smooth
products `X × Y` and `X × Y × Z`, and proper pushforward along the projections.

## Main definitions

* `Stacks.WeilCohomology.rationalFlatPullback`, `Stacks.WeilCohomology.rationalProperPushforward`
  and `Stacks.WeilCohomology.rationalDegreeEquiv`: flat pullback, proper pushforward and
  reindexing on rational Chow groups.
* `Stacks.WeilCohomology.diagonalGysinClass`: the Gysin class `Δ^!` of the diagonal of a smooth
  separated scheme, built from its normal bundle by the construction of Stacks 0FBK.
* `Stacks.WeilCohomology.rationalIntersectionProduct`: the intersection product of Stacks 0FC0
  on the rational Chow groups of a smooth separated scheme `W`, `α · β = Δ^!(α × β)`.
* `Stacks.WeilCohomology.correspondencePushforwardOfDimension`: `c ↦ c_*`.
* `Stacks.WeilCohomology.correspondenceCompOfDimension`: `(c', c) ↦ c' ∘ c`.

## Implementation notes

**Nothing is carried.** Flat pullback descends to Chow groups by the general case of Stacks
02S1, `Stacks.Chow.flatPullbackChowOfRelativeDimension`; proper pushforward descends by Stacks
02S2, `Stacks.Chow.properPushforwardDescends`; and the intersection product of Stacks 0FC0,
`Stacks.Chow.intersectionProduct`, is formed with an actual bivariant class: the degree-`n`
part `Stacks.Chow.VirtualNormalBundle.degreeClass` of the class `c(Δ, 𝒩)` of Stacks 0FBK, for
`𝒩` the normal bundle of the diagonal, which is a regular immersion because the scheme is smooth
(`Stacks.Chow.isRegularImmersion_diagonal_of_smooth`, Stacks 0FBR), with the normal bundle
`Stacks.Chow.VirtualNormalBundle.ofIsRegularImmersion`. That class is the Gysin map `Δ^!` of
Section 42.59: for a smooth scheme of relative dimension `n` the normal bundle of the diagonal has
rank `n`, and then `c(Δ, 𝒩)` lies in degree `n` (Stacks 0FBK (3)). None of the definitions below
takes a hypothesis that is a result.

**Gradings.** This repository grades Chow groups by dimension. For `X` equidimensional of
dimension `d` the codimension grading is `CH^i(X) = A_{d - i}(X)`, which is
`Stacks.WeilCohomology.RationalChowGroupCodim`, and a correspondence of degree `r` from `X` to `Y`,
`Y` of dimension `e`, is an element of `A_{e - r}(X × Y) ⊗ ℚ`, which is
`Stacks.WeilCohomology.Correspondence`. The dimensions are recorded as instances
`SmoothOfRelativeDimension d sX`, so that they are a property of `X` and not a free parameter;
the projection `X × Y ⟶ X` is then smooth of relative dimension `e`, which is what flat pullback
along it needs. The degrees in the source are equal integers written differently on the two
sides (`(e - r) + (d - i + e) - (d + e) = e - (i + r)`), and the identification is made by
`rationalDegreeEquiv` at the end; so that no further reindexing is needed downstream, both
operations take the target degree as an argument together with the equation that computes it.

**The general case.** Stacks writes a smooth projective `X` as the disjoint union of its
equidimensional open and closed pieces `X_d`, and every operation of Section 0FFZ is defined
piece by piece. The pieces are formed, and the operations assembled from the ones here, in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Motives.ChowGroupsOfMotives`.

## References

* [Stacks Project, Section 0FFZ](https://stacks.math.columbia.edu/tag/0FFZ)
* [Stacks Project, Tag 0FC0](https://stacks.math.columbia.edu/tag/0FC0)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBR](https://stacks.math.columbia.edu/tag/0FBR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace AlgebraicGeometry

/-- A morphism smooth of relative dimension `n` has relative dimension `n` in the sense of
Stacks 02NJ: the dimension of the fibre through every point of the source is `n`. -/
theorem relativeDimension_of_smoothOfRelativeDimension {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
    [SmoothOfRelativeDimension n f] [LocallyOfFiniteType f] : RelativeDimension f n :=
  relativeDimension_of_open_square (𝟙 X) f f (𝟙 S) (by simp) fun x =>
    fiberDimensionAt_eq_of_smoothOfRelativeDimension f n x

/-- Smooth of relative dimension `n` is stable under base change: the first projection
`X ×_S Y ⟶ X` is smooth of relative dimension `n` when `Y ⟶ S` is. -/
instance smoothOfRelativeDimension_pullback_fst {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (n : ℕ) [SmoothOfRelativeDimension n g] : SmoothOfRelativeDimension n (pullback.fst f g) :=
  (smoothOfRelativeDimension_isStableUnderBaseChange (n := n)).of_isPullback
    (IsPullback.of_hasPullback f g).flip ‹_›

/-- Smooth of relative dimension `n` is stable under base change: the second projection
`X ×_S Y ⟶ Y` is smooth of relative dimension `n` when `X ⟶ S` is. -/
instance smoothOfRelativeDimension_pullback_snd {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (n : ℕ) [SmoothOfRelativeDimension n f] : SmoothOfRelativeDimension n (pullback.snd f g) :=
  (smoothOfRelativeDimension_isStableUnderBaseChange (n := n)).of_isPullback
    (IsPullback.of_hasPullback f g) ‹_›

end AlgebraicGeometry

namespace Stacks.WeilCohomology

/-! ### Operations on rational Chow groups -/

section Rational

variable (C : ChowSituation.{u})

/-- Reindexing a rational Chow group along an equality of degrees. -/
def rationalDegreeEquiv {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] {a b : ℤ}
    (h : a = b) : RationalChowGroup C sX a ≃ₗ[ℚ] RationalChowGroup C sX b :=
  LinearEquiv.baseChange ℤ ℚ _ _ (chowGroupDegreeEquiv C sX h).toIntLinearEquiv

/-- Flat pullback `f^* : A_a(X) ⊗ ℚ ⟶ A_{a + r}(X') ⊗ ℚ` along a morphism flat of relative
dimension `r`, the rationalisation of `Stacks.Chow.flatPullbackChowOfRelativeDimension`. -/
def rationalFlatPullback {X' X : Scheme.{u}} (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX']
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f]
    (hbase : f ≫ sX = sX') (r : ℕ) (hf : RelativeDimension f r) (a : ℤ) :
    RationalChowGroup C sX a →ₗ[ℚ] RationalChowGroup C sX' (a + r) :=
  LinearMap.baseChange ℚ
    (flatPullbackChowOfRelativeDimension C sX' sX f hbase r hf a).toIntLinearMap

/-- Proper pushforward `p_* : A_a(X) ⊗ ℚ ⟶ A_a(Y) ⊗ ℚ` along a proper morphism, the
rationalisation of `Stacks.Chow.properChowPushforward`, which descends to Chow groups by Stacks
02S2. -/
def rationalProperPushforward {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (p : X ⟶ Y) [IsProper p] (hp : p ≫ sY = sX)
    (a : ℤ) : RationalChowGroup C sX a →ₗ[ℚ] RationalChowGroup C sY a :=
  LinearMap.baseChange ℚ
    (properChowPushforward C sX sY p hp a (properPushforwardDescends C sX sY p hp a)).toIntLinearMap

end Rational

/-! ### The intersection product on a smooth scheme -/

section Intersection

variable (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
  {W : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW] [Smooth sW] [IsSeparated sW]

/-- **The Gysin class `Δ^!` of the diagonal** `Δ : W ⟶ W ×_S W` of a smooth separated scheme, in
degree `n`. The diagonal is a closed immersion because `W` is separated and a regular immersion
because `W` is smooth (Stacks 0FBR); its normal bundle `𝒩` is a virtual normal bundle, and this is
the degree-`n` part of the class `c(Δ, 𝒩)` of Stacks 0FBK. For `W` smooth of relative dimension
`n` that is all of `c(Δ, 𝒩)`, the normal bundle having rank `n` (Stacks 0FBK (3)), i.e. it is the
Gysin map `Δ^!` of Section 42.59. -/
def diagonalGysinClass (n : ℤ) :
    BivariantClass C (gysinSystemOfInvertible C) sW (selfProductStructure C sW)
      (pullback.diagonal sW) (diagonal_comp_selfProductStructure C sW) n :=
  letI := LocallyOfFiniteType.isLocallyNoetherian sW
  letI := LocallyOfFiniteType.isLocallyNoetherian (selfProductStructure C sW)
  (VirtualNormalBundle.ofIsRegularImmersion (pullback.diagonal sW)
      (isRegularImmersion_diagonal_of_smooth sW)).degreeClass C (selfProductStructure C sW) sW
    (diagonal_comp_selfProductStructure C sW) n

/-- The intersection product of Stacks 0FC0 on the Chow groups of `W` itself, with integral
coefficients: `α · β = Δ^!(α × β)` read on `W ×_W W = W`, for the Gysin class
`Stacks.WeilCohomology.diagonalGysinClass` of degree `n`. -/
def chowIntersectionProduct (n a b : ℤ) :
    TensorProduct ℤ (chowGroup C sW a) (chowGroup C sW b) →ₗ[ℤ] chowGroup C sW (a + b - n) :=
  ((chowGroupSelfProductUnitCollapse C sW (a + b - n)).toAddMonoidHom.comp
    ((intersectionProduct C hδ (gysinSystemOfInvertible C) sW (𝟙 W) (𝟙 W) n
        (diagonalGysinClass C sW n) a b).comp
      (TensorProduct.map
        (chowGroupCongr C (Category.id_comp sW).symm a).toIntLinearEquiv.toLinearMap
        (chowGroupCongr C (Category.id_comp sW).symm b).toIntLinearEquiv.toLinearMap
        ).toAddMonoidHom)).toIntLinearMap

/-- **The intersection product of Stacks 0FC0 on rational Chow groups** of a smooth separated
scheme `W`, as a `ℚ`-bilinear map `A_a(W) ⊗ ℚ → A_b(W) ⊗ ℚ → A_{a + b - n}(W) ⊗ ℚ`: the
rationalisation of `α · β = Δ^!(α × β)`, with `Δ^!` the Gysin class of the diagonal in degree `n`
(`Stacks.WeilCohomology.diagonalGysinClass`), which for `W` smooth of relative dimension `n` is
the intersection product of the source. -/
def rationalIntersectionProduct (n a b : ℤ) :
    RationalChowGroup C sW a →ₗ[ℚ] RationalChowGroup C sW b →ₗ[ℚ]
      RationalChowGroup C sW (a + b - n) :=
  TensorProduct.curry
    ((LinearMap.baseChange ℚ (chowIntersectionProduct C hδ sW n a b)).comp
      (TensorProduct.AlgebraTensorModule.distribBaseChange ℤ ℚ _ _).symm.toLinearMap)

end Intersection

/-! ### The action of a correspondence -/

section Action

variable (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
  {X Y : Scheme.{u}} (sX : X ⟶ C.S) (sY : Y ⟶ C.S) [LocallyOfFiniteType sX]
  [LocallyOfFiniteType sY] (d e : ℕ) [SmoothOfRelativeDimension d sX]
  [SmoothOfRelativeDimension e sY] [IsProper sX] [IsProper sY]

/-- **The pushforward action of a correspondence**, Section 0FFZ: for `X` and `Y` smooth and
proper over the base, of dimensions `d` and `e`, a correspondence `c ∈ Corrʳ(X, Y)` acts by

  `c_*(α) = pr₂,*(c · pr₁^* α)`,   `CH^i(X) ⊗ ℚ ⟶ CH^j(Y) ⊗ ℚ`,   `j = i + r`,

flat pullback along the first projection `X × Y ⟶ X` (smooth of relative dimension `e`), the
intersection product of Stacks 0FC0 on the smooth scheme `X × Y` of dimension `d + e`, and proper
pushforward along the second projection `X × Y ⟶ Y` (proper since `X` is). It is `ℚ`-bilinear
in `c` and `α`. -/
def correspondencePushforwardOfDimension (r i j : ℤ) (h : i + r = j) :
    Correspondence C sX sY e r →ₗ[ℚ]
      RationalChowGroupCodim C sX d i →ₗ[ℚ] RationalChowGroupCodim C sY e j :=
  haveI := SmoothOfRelativeDimension.smooth d sX
  haveI := SmoothOfRelativeDimension.smooth e sY
  LinearMap.compr₂
    ((rationalIntersectionProduct C hδ (pullback.fst sX sY ≫ sX) ((d : ℤ) + e) (e - r)
        (d - i + e)).compl₂
      (rationalFlatPullback C (pullback.fst sX sY ≫ sX) sX (pullback.fst sX sY) rfl e
        (relativeDimension_of_smoothOfRelativeDimension (pullback.fst sX sY) e) (d - i)))
    ((rationalDegreeEquiv C sY (by rw [← h]; ring)).toLinearMap ∘ₗ
      rationalProperPushforward C (pullback.fst sX sY ≫ sX) sY (pullback.snd sX sY)
        pullback.condition.symm _)

end Action

/-! ### The triple product -/

section TripleProduct

variable {S X Y Z : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) (sZ : Z ⟶ S)

/-- The projection `pr₁₂ : X × Y × Z ⟶ X × Y`, the triple product being
`(X × Y) ×_Y (Y × Z)`. -/
abbrev tripleProj₁₂ :
    (pullback (pullback.snd sX sY) (pullback.fst sY sZ) : Scheme.{u}) ⟶ pullback sX sY :=
  pullback.fst (pullback.snd sX sY) (pullback.fst sY sZ)

/-- The projection `pr₂₃ : X × Y × Z ⟶ Y × Z`. -/
abbrev tripleProj₂₃ :
    (pullback (pullback.snd sX sY) (pullback.fst sY sZ) : Scheme.{u}) ⟶ pullback sY sZ :=
  pullback.snd (pullback.snd sX sY) (pullback.fst sY sZ)

/-- The structure morphism of the triple product `X × Y × Z` over the base. -/
abbrev tripleStructure : (pullback (pullback.snd sX sY) (pullback.fst sY sZ) : Scheme.{u}) ⟶ S :=
  tripleProj₁₂ sX sY sZ ≫ pullback.fst sX sY ≫ sX

/-- The composite `X × Y × Z ⟶ Y × Z ⟶ Y ⟶ S` is the structure morphism of the triple product. -/
theorem tripleProj₂₃_comp_structure :
    tripleProj₂₃ sX sY sZ ≫ pullback.fst sY sZ ≫ sY = tripleStructure sX sY sZ := by
  rw [tripleStructure, ← Category.assoc, ← pullback.condition, Category.assoc,
    ← pullback.condition]

/-- The composites `X × Y × Z ⟶ X ⟶ S` and `X × Y × Z ⟶ Z ⟶ S` agree. -/
theorem tripleProj_comp_comp :
    (tripleProj₁₂ sX sY sZ ≫ pullback.fst sX sY) ≫ sX =
      (tripleProj₂₃ sX sY sZ ≫ pullback.snd sY sZ) ≫ sZ := by
  rw [Category.assoc, pullback.condition (f := sX), ← Category.assoc,
    pullback.condition (f := pullback.snd sX sY), Category.assoc, pullback.condition (f := sY),
    Category.assoc]

/-- The projection `pr₁₃ : X × Y × Z ⟶ X × Z`. -/
abbrev tripleProj₁₃ :
    (pullback (pullback.snd sX sY) (pullback.fst sY sZ) : Scheme.{u}) ⟶ pullback sX sZ :=
  pullback.lift (tripleProj₁₂ sX sY sZ ≫ pullback.fst sX sY)
    (tripleProj₂₃ sX sY sZ ≫ pullback.snd sY sZ) (tripleProj_comp_comp sX sY sZ)

/-- The composite `X × Y × Z ⟶ X × Z ⟶ X ⟶ S` is the structure morphism of the triple product. -/
theorem tripleProj₁₃_comp_structure :
    tripleProj₁₃ sX sY sZ ≫ pullback.fst sX sZ ≫ sX = tripleStructure sX sY sZ := by
  rw [tripleStructure, ← Category.assoc, pullback.lift_fst, Category.assoc]

/-- The projection `pr₁₃` of a triple product of proper schemes is proper. -/
instance isProper_tripleProj₁₃ [IsProper sX] [IsProper sY] [IsProper sZ] :
    IsProper (tripleProj₁₃ sX sY sZ) := by
  have : IsProper (tripleProj₁₃ sX sY sZ ≫ pullback.fst sX sZ ≫ sX) := by
    rw [tripleProj₁₃_comp_structure]
    infer_instance
  exact IsProper.of_comp _ (pullback.fst sX sZ ≫ sX)

end TripleProduct

/-! ### Composition of correspondences -/

section Composition

variable (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
  {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) (sY : Y ⟶ C.S) (sZ : Z ⟶ C.S) [LocallyOfFiniteType sX]
  [LocallyOfFiniteType sY] [LocallyOfFiniteType sZ]

variable (d e f : ℕ) [SmoothOfRelativeDimension d sX] [SmoothOfRelativeDimension e sY]
  [SmoothOfRelativeDimension f sZ] [IsProper sX] [IsProper sY] [IsProper sZ]

/-- **Composition of correspondences**, Section 0FFZ: for `X`, `Y` and `Z` smooth and proper over
the base, of dimensions `d`, `e` and `f`, and correspondences `c ∈ Corrʳ(X, Y)` and
`c' ∈ Corrˢ(Y, Z)`,

  `c' ∘ c = pr₁₃,*(pr₁₂^* c · pr₂₃^* c') ∈ Corrᵗ(X, Z)`,   `t = r + s`,

flat pullback along the projections `pr₁₂` (smooth of relative dimension `f`) and `pr₂₃` (smooth
of relative dimension `d`) of `X × Y × Z`, the intersection product of Stacks 0FC0 on the smooth
scheme `X × Y × Z` of dimension `d + e + f`, and proper pushforward along `pr₁₃` (proper since `Y`
is). It is `ℚ`-bilinear in `c'` and `c`. -/
def correspondenceCompOfDimension (r s t : ℤ) (h : r + s = t) :
    Correspondence C sY sZ f s →ₗ[ℚ] Correspondence C sX sY e r →ₗ[ℚ]
      Correspondence C sX sZ f t :=
  haveI := SmoothOfRelativeDimension.smooth d sX
  haveI := SmoothOfRelativeDimension.smooth e sY
  haveI := SmoothOfRelativeDimension.smooth f sZ
  LinearMap.compr₂
    (((rationalIntersectionProduct C hδ (tripleStructure sX sY sZ) ((d : ℤ) + e + f)
        (e - r + f) (f - s + d)).compl₁₂
      (rationalFlatPullback C (tripleStructure sX sY sZ) (pullback.fst sX sY ≫ sX)
        (tripleProj₁₂ sX sY sZ) rfl f
        (relativeDimension_of_smoothOfRelativeDimension (tripleProj₁₂ sX sY sZ) f) (e - r))
      (rationalFlatPullback C (tripleStructure sX sY sZ) (pullback.fst sY sZ ≫ sY)
        (tripleProj₂₃ sX sY sZ) (tripleProj₂₃_comp_structure sX sY sZ) d
        (relativeDimension_of_smoothOfRelativeDimension (tripleProj₂₃ sX sY sZ) d)
        (f - s))).flip)
    ((rationalDegreeEquiv C (pullback.fst sX sZ ≫ sX) (by rw [← h]; ring)).toLinearMap ∘ₗ
      rationalProperPushforward C (tripleStructure sX sY sZ) (pullback.fst sX sZ ≫ sX)
        (tripleProj₁₃ sX sY sZ) (tripleProj₁₃_comp_structure sX sY sZ) _)

end Composition

end Stacks.WeilCohomology

end

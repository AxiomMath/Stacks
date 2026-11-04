module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernClassCapAdditive
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackOrderOfVanishing

/-!
# Flat pullback and the first Chern class cap product on an algebraic space

In the situation of Stacks 0EDT let `X/B` and `Y/B` be good, let `f : X ⟶ Y` be flat of
relative dimension `r`, let `ℒ` be an invertible `O_Y`-module and let `α` be a `(k+1)`-cycle on
`Y`.  Stacks 0EQR is the identity

  `f^*(c₁(ℒ) ∩ α) = c₁(f^*ℒ) ∩ f^*α`.

This file proves it, at the level of cycles, from the pointwise Stacks 0EQQ of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackOrderOfVanishing`.

## Main definitions

* `AlgebraicGeometry.Space.FlatCyclePullback`: the flat pullback of cycles of Stacks 0EP8,
  carried as data *together with its defining formula* — a multiplicity `m_{T,f^{-1}(W)}` for
  each integral closed subspace `W ⊆ Y` and each integral closed subspace `T ⊆ X`, and the
  statement that the coefficient of `f^*α` at `T` is `∑ α_W · m_{T,f^{-1}(W)}`.  This is what
  Stacks 0EP8 says `f^*` *is*: on an integral closed subspace it is the cycle of the inverse
  image, with the multiplicities of that inverse image, and on a general cycle it is the
  resulting locally finite sum.
* `AlgebraicGeometry.Space.FlatChernDivisorComparison`: the comparison datum at one integral
  closed subspace `W ⊆ Y` of δ-dimension `k + 1`, assembling what the source's proof writes
  down: the nonzero meromorphic section `s` of `ℒ|_W` presenting `c₁(ℒ|_W) ∩ [W]`, the inverse
  image `f^{-1}(W)`, the section `f^*s` presenting `c₁(f^*ℒ|_{f^{-1}(W)}) ∩ [f^{-1}(W)]`, and
  at each prime divisor of `f^{-1}(W)` the flat local homomorphism of henselian local rings over
  the prime divisor of `W` beneath it, with the multiplicity Stacks 0EP8 attaches to it.

## Main results

* `AlgebraicGeometry.Space.flatCyclePullback_mult_firstChernComponentCycle`: the case of a
  single integral closed subspace, which is the whole content: the flat pullback of the
  component cycle of `W` and the component cycle of the inverse image of `W` agree at every
  coefficient.  Nothing about either is assumed; the identity of the two coefficients *is* the
  pointwise Stacks 0EQQ.
* `AlgebraicGeometry.Space.flatCyclePullback_firstChernCapCycleMap`: **Stacks 0EQR**, at the
  level of cycles.
* `AlgebraicGeometry.Space.flatPullback_firstChernClassCap`: **Stacks 0EQR**, in the Chow groups,
  which is the source's own grading of the statement.

## Implementation notes

### What is carried and what is proved

The commutation of the flat pullback with the cap product is the assertion of Stacks 0EQR, so it
is *not* assumed in any form.  What is carried is the flat pullback itself, together with the
formula that defines it, `AlgebraicGeometry.Space.FlatCyclePullback.coeff`.  The pullback is
*not* missing from the repository — Stacks 0EP8 is built as
`AlgebraicGeometry.Space.flatCyclePullback`, which inhabits
`AlgebraicGeometry.Space.FlatCyclePullback`, so the statements below can be instantiated at the
constructed operation; what keeps them from being Stacks 0EQR outright is the comparison datum
below, not this parameter.  Carrying an
arbitrary additive map and assuming that it commutes with the cap product would be assuming the
lemma; carrying the defining formula and deriving the commutation is the lemma.  The same choice
is made in `StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernClassCapAdditive` for Stacks
0EQK, which carries `AlgebraicGeometry.Space.IsDivisorPresentation` — the definition Stacks 0EQE
would supply — and derives additivity from the pointwise Stacks 0EPV.  This file is the same
move with Stacks 0EQQ in place of Stacks 0EPV.

Three further things are carried, and each is upstream of the statement rather than part of it.

* The component rules of Stacks 0EQJ on `Y` and on `X`, with the Weil divisor presentations of
  Stacks 0EQE, exactly as in the file for Stacks 0EQK.  The two sheaves `ℒ|_W` and
  `f^*ℒ|_{f^{-1}(W)}` and their sections `s` and `f^*s` are unconstrained parameters, as they
  are in the carried Stacks 0EQQ.  Both do exist in this repository — the inverse image of
  modules along any morphism of algebraic spaces is `AlgebraicGeometry.Space.modulePullback`
  (Stacks 03LU) and the pullback of a global meromorphic section is Stacks 0ENC, part (1), as
  `AlgebraicGeometry.Space.pullbackMeromorphicSection` — but what the comparison needs is
  the identity `ratio_preimage` below, that the canonical ratio of `f^*s` at the generic point
  of `T` is the image of the ratio of `s` under the henselian local homomorphism, and that
  compatibility is not proved here; the hypothesis on the ratios at the generic points stands in
  for it, and it is the source's own step of writing `s/s_ξ = a/b` and pulling the fraction
  back.
* The flat local homomorphism `φ : O^h_{Y,ξ'} ⟶ O^h_{X,ξ}` of henselian local rings at the
  generic points of a prime divisor and of a prime divisor over it, with its locality and
  flatness.  This is the hypothesis shape of the carried Stacks 0EQA and Stacks 0EQQ.  Such a
  homomorphism *is* available: it is
  `AlgebraicGeometry.Space.PrimeDivisor.exists_genericHenselianLocalRingHom` of
  `StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRingMap`, produced existentially,
  with its locality and its flatness.  What that lemma does not pin down is its compatibility
  with the pullback of meromorphic sections, which is exactly what `ratio_preimage` asks for, so
  the homomorphism is carried here together with that compatibility rather than chosen.
* The identification of the multiplicity that Stacks 0EP8 attaches to a prime divisor `T` of
  `f^{-1}(W)` in `f^*[Z']`, for `Z'` the prime divisor of `W` beneath `T`, with the colength
  `AlgebraicGeometry.Space.primeDivisorFlatMultiplicity` that Stacks 02M1 computes with.  Stacks
  0EE9 reads a multiplicity as the length of a stalk and along a flat morphism that length is
  this colength; the identification is not proved in this repository, as the implementation
  notes of `StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackOrderOfVanishing` record.

What is proved is the commutation.  At a single integral closed subspace `W` it is
`AlgebraicGeometry.Space.flatCyclePullback_mult_firstChernComponentCycle`: both coefficients
collapse to a single term, and those two terms are equal by Stacks 0EQQ,
`AlgebraicGeometry.Space.orderOfVanishingSection_eq_multiplicity_mul`.  The passage from there
to a general cycle is the locally finite bookkeeping that the source performs by appealing to
Remark 0EQ8, and it is carried out here: the two double sums are exchanged, which needs the
local finiteness of the cycle `α`, of the component cycles, and the containment of the support
of `f^*[W]` in `f^{-1}(W)`.

### Why the inverse image is assumed integral

The source writes the irreducible components `W'_i` of `W' = f^{-1}(W)` of δ-dimension `k + r`
and uses `[W']_{k+r} = ∑ n_i [W'_i]`, so that the cycle identity on `W'` is a sum over those
components.  The step from the pointwise Stacks 0EQQ to that sum is the additivity over the
irreducible components of the multiplicities of Stacks 0EE2 and Stacks 0EE9, which this
repository does not have — the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackOrderOfVanishing` record it as the one
step its coefficientwise statements leave uncovered.  The comparison datum below therefore asks
the inverse image of each integral closed subspace occurring in `α` to be integral, which is the
case `i = 1`, `n_1 = 1` of the source's sum and the only case in which the pointwise lemma
suffices.  The restriction is named in the attribute clauses.

### The grading

A `AlgebraicGeometry.Space.CycleGroup` is never transported along an equality of degrees.  The
flat pullback is therefore carried as a map `Z_m(Y) ⟶ Z_n(X)` for any pair with `m + r = n`,
with the degree equality an explicit argument, so that the two gradings `(k+1) + r` and
`(k+r) + 1` occurring in the statement are both available without a cast.

## References

* [Stacks Project, Tag 0EQR](https://stacks.math.columbia.edu/tag/0EQR)
* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDZ](https://stacks.math.columbia.edu/tag/0EDZ)
* [Stacks Project, Tag 0EE2](https://stacks.math.columbia.edu/tag/0EE2)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EP5](https://stacks.math.columbia.edu/tag/0EP5)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPV](https://stacks.math.columbia.edu/tag/0EPV)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
* [Stacks Project, Tag 0EQA](https://stacks.math.columbia.edu/tag/0EQA)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQK](https://stacks.math.columbia.edu/tag/0EQK)
* [Stacks Project, Tag 0EQQ](https://stacks.math.columbia.edu/tag/0EQQ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u w v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] Classical.propDecidable

/-! ### Exchanging two locally finite sums

The passage from one integral closed subspace to an arbitrary cycle exchanges a sum over the
subspaces occurring in the cycle with a sum over the subspaces occurring in its image.  Both
sums are infinite, and the exchange is legitimate because the terms vanish outside a product of
two finite sets. -/

/-- Exchanging two sums over types whose joint terms vanish outside a product of two finite
sets. -/
public theorem finsum_exchange_of_vanishing {ι κ : Type*} (F : ι → κ → ℤ)
    {A : Set ι} {Bs : Set κ} (hA : A.Finite) (hB : Bs.Finite)
    (hvan : ∀ (i : ι) (j : κ), F i j ≠ 0 → i ∈ A ∧ j ∈ Bs) :
    (∑ᶠ i : ι, ∑ᶠ j : κ, F i j) = ∑ᶠ j : κ, ∑ᶠ i : ι, F i j := by
  have hrow : ∀ i : ι, (∑ᶠ j : κ, F i j) = ∑ᶠ j ∈ Bs, F i j := fun i =>
    (finsum_mem_univ fun j => F i j).symm.trans
      (finsum_mem_inter_support_eq' (fun j => F i j) Set.univ Bs fun j hj =>
        ⟨fun _ => (hvan i j hj).2, fun _ => Set.mem_univ j⟩)
  have hcol : ∀ j : κ, (∑ᶠ i : ι, F i j) = ∑ᶠ i ∈ A, F i j := fun j =>
    (finsum_mem_univ fun i => F i j).symm.trans
      (finsum_mem_inter_support_eq' (fun i => F i j) Set.univ A fun i hi =>
        ⟨fun _ => (hvan i j hi).1, fun _ => Set.mem_univ i⟩)
  have houtl : (∑ᶠ i : ι, ∑ᶠ j ∈ Bs, F i j) = ∑ᶠ i ∈ A, ∑ᶠ j ∈ Bs, F i j :=
    (finsum_mem_univ fun i => ∑ᶠ j ∈ Bs, F i j).symm.trans
      (finsum_mem_inter_support_eq' (fun i => ∑ᶠ j ∈ Bs, F i j) Set.univ A fun i hi =>
        ⟨fun _ => by
          obtain ⟨j, -, hj⟩ := exists_ne_zero_of_finsum_mem_ne_zero hi
          exact (hvan i j hj).1, fun _ => Set.mem_univ i⟩)
  have houtr : (∑ᶠ j : κ, ∑ᶠ i ∈ A, F i j) = ∑ᶠ j ∈ Bs, ∑ᶠ i ∈ A, F i j :=
    (finsum_mem_univ fun j => ∑ᶠ i ∈ A, F i j).symm.trans
      (finsum_mem_inter_support_eq' (fun j => ∑ᶠ i ∈ A, F i j) Set.univ Bs fun j hj =>
        ⟨fun _ => by
          obtain ⟨i, -, hi⟩ := exists_ne_zero_of_finsum_mem_ne_zero hj
          exact (hvan i j hi).2, fun _ => Set.mem_univ j⟩)
  rw [finsum_congr hrow, houtl, finsum_congr hcol, houtr, finsum_mem_comm F hA hB]

/-! ### The image of an integral closed subspace of an integral closed subspace -/

section Image

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)

/-- The image in `X` of an integral closed subspace of an integral closed subspace `W ⊆ X`,
along the closed immersion `W → X`. -/
abbrev integralClosedSubspaceImage
    (Z : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor) :
    IntegralClosedSubspace D.site D.base D.base_mem X :=
  IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 W.isClosedSubspace.1
    (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 Z

/-- Taking the image in `X` of an integral closed subspace of `W` is injective. -/
theorem injective_integralClosedSubspaceImage :
    Function.Injective (integralClosedSubspaceImage D sX hX W) :=
  IntegralClosedSubspace.injective_pushforward D.site D.base D.base_mem hX.1
    W.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2

variable (k : ℤ) (chern : FirstChernComponentCycleRule D sX k)

/-- The coefficient of the component cycle of `W` at the image of an integral closed subspace
of `W` is the coefficient of the component cycle on `W` there. -/
theorem firstChernComponentCycle_apply_image (hW : deltaDimension D sX W = k + 1)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor) :
    (firstChernComponentCycle D sX hX k chern W).1
        (integralClosedSubspaceImage D sX hX W Z) = (chern W hW).1 Z := by
  rw [firstChernComponentCycle_of_deltaDimension_eq D sX hX k chern hW]
  exact cycleClosedPushforward_apply_pushforward D hX.1 W.isClosedSubspace.1
    (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 (chern W hW).1 Z

/-- The component cycle of `W` vanishes at an integral closed subspace of `X` which is not the
image of one of `W`. -/
theorem firstChernComponentCycle_apply_eq_zero_of_forall_ne
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : ∀ Z' : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor,
      integralClosedSubspaceImage D sX hX W Z' ≠ Z) :
    (firstChernComponentCycle D sX hX k chern W).1 Z = 0 := by
  by_cases hW : deltaDimension D sX W = k + 1
  · rw [firstChernComponentCycle_of_deltaDimension_eq D sX hX k chern hW]
    exact cycleClosedPushforward_apply_of_forall_ne D hX.1 W.isClosedSubspace.1
      (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 (chern W hW).1 Z hZ
  · rw [firstChernComponentCycle_of_deltaDimension_ne D sX hX k chern hW]
    rfl

end Image

/-! ### The flat pullback of cycles, carried with its defining formula -/

section Pullback

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **Stacks 0EP8, carried as data together with its defining formula.** The flat pullback of
cycles along a morphism `f : X ⟶ Y` of good algebraic spaces over `B` which is flat of relative
dimension `r`, which this repository does not construct.

The datum is a multiplicity `mult W T` for an integral closed subspace `W ⊆ Y` and an integral
closed subspace `T ⊆ X` — the multiplicity of `T` in the scheme-theoretic inverse image
`f^{-1}(W)`, so that `f^*[W] = [f^{-1}(W)]_{k+r}` is the coefficient family `mult W` — together
with the maps `f^* : Z_m(Y) ⟶ Z_n(X)` for `m + r = n` and the statement `coeff` that the
coefficient of `f^*α` at `T` is `∑ α_W · mult W T`, which is parts (1) and (2) of the source.
The field `mult_support` is that `f^*[W]` is carried by `f^{-1}(W)`. -/
structure FlatCyclePullback (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (f : X ⟶ Y) (r : ℕ) where
  /-- **Stacks 0EP8, part (1).** The multiplicity of an integral closed subspace `T ⊆ X` in the
  inverse image `f^{-1}(W)` of an integral closed subspace `W ⊆ Y`, that is the coefficient of
  `T` in the cycle `f^*[W] = [f^{-1}(W)]_{k+r}`. -/
  mult : IntegralClosedSubspace D.site D.base D.base_mem Y →
    IntegralClosedSubspace D.site D.base D.base_mem X → ℤ
  /-- **Stacks 0EP8, part (3).** The flat pullback of cycles, as an additive map raising the
  δ-dimension by `r`. -/
  map : ∀ m n : ℤ, m + (r : ℤ) = n → (CycleGroup D sY m →+ CycleGroup D sX n)
  /-- **Stacks 0EP8, parts (1) and (2).** The coefficient of `f^*α` at an integral closed
  subspace `T ⊆ X` is the sum of `α_W` times the multiplicity of `T` in `f^{-1}(W)`. -/
  coeff : ∀ (m n : ℤ) (hmn : m + (r : ℤ) = n) (α : CycleGroup D sY m)
      (T : IntegralClosedSubspace D.site D.base D.base_mem X),
    (map m n hmn α).1 T =
      ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem Y, α.1 W * mult W T
  /-- `f^*[W]` is carried by `f^{-1}(W)`: a subspace with a nonzero multiplicity has its generic
  point over a point of `W`. -/
  mult_support : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
      (T : IntegralClosedSubspace D.site D.base D.base_mem X), mult W T ≠ 0 →
    pointsMap D.site D.base D.base_mem X f (T.ambientGenericPoint D.site D.base D.base_mem) ∈
      subspacePointSet D.site D.base D.base_mem Y W.subspace

end Pullback

section PullbackLemmas

variable {D : BaseSpaceDimensionSituation.{u}}
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {sX : X ⟶ D.space} {hX : D.IsGood sX} {sY : Y ⟶ D.space} {hY : D.IsGood sY}
    {f : X ⟶ Y} {r : ℕ} (pb : FlatCyclePullback D sX hX sY hY f r)

/-- The coefficient of the flat pullback of the cycle of a single integral closed subspace
`W ⊆ Y` is the multiplicity in `f^{-1}(W)`: this is part (1) of the source, read off from the
defining formula. -/
theorem FlatCyclePullback.apply_integralCycle (m n : ℤ) (hmn : m + (r : ℤ) = n)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (hW : deltaDimension D sY W = m)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (pb.map m n hmn (integralCycle D sY m W hW)).1 T = pb.mult W T := by
  rw [pb.coeff m n hmn, finsum_eq_single _ W fun W' hW' => by
      rw [integralCycle_coe, integralCycleCoeff_eq_zero D W hW', zero_mul],
    integralCycle_coe, integralCycleCoeff_self, one_mul]

/-- A subspace of `X` with a nonzero multiplicity in `f^{-1}(W)` has δ-dimension `r` more than
`W`: the flat pullback of a `k`-cycle is a `(k+r)`-cycle. -/
theorem FlatCyclePullback.deltaDimension_eq_of_mult_ne_zero
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X) (hT : pb.mult W T ≠ 0) :
    deltaDimension D sX T = deltaDimension D sY W + (r : ℤ) := by
  have hcoeff := pb.apply_integralCycle (deltaDimension D sY W)
    (deltaDimension D sY W + (r : ℤ)) rfl W rfl T
  exact (pb.map (deltaDimension D sY W) (deltaDimension D sY W + (r : ℤ)) rfl
    (integralCycle D sY (deltaDimension D sY W) W rfl)).2.2 T (by rw [hcoeff]; exact hT)

end PullbackLemmas

/-! ### The comparison datum at one integral closed subspace -/

section Comparison

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The comparison datum of the source's proof of Stacks 0EQR at a single integral closed
subspace `W ⊆ Y` of δ-dimension `k + 1`.

The source chooses a nonzero meromorphic section `s` of `ℒ|_W`, forms `W' = f^{-1}(W)` and the
restrictions `s_i` of `s` to the irreducible components of `W'`, and compares the orders of
vanishing.  The fields below are exactly those choices, with the inverse image taken integral:
the sheaf, section and ratio on `W` presenting the component cycle of `W` by Stacks 0EQE; the
inverse image `preimage` together with the multiplicities Stacks 0EP8 attaches to it; the sheaf,
section and ratio on the inverse image presenting its component cycle; and at each prime divisor
`T` of the inverse image the prime divisor `base T` of `W` beneath it, the flat local
homomorphism `hom T` of the henselian local rings at their generic points, the multiplicity, the
fraction `num T / den T` representing the ratio of `s` at the generic point of `base T`, and the
statement that the ratio of the pulled-back section at the generic point of `T` is the image of
that fraction under `hom T`. -/
structure FlatChernDivisorComparison (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (f : X ⟶ Y) (r : ℕ) (k : ℤ)
    (pb : FlatCyclePullback D sX hX sY hY f r)
    (setupY : SubspaceDivisorSetup D Y) (setupX : SubspaceDivisorSetup D X)
    [∀ (V : IntegralClosedSubspace D.site D.base D.base_mem Y)
      (P : PrimeDivisor D.site D.base D.base_mem V.subspace.toFunctor),
      IsLocalRing ↥(P.genericHenselianLocalRing D.site D.base D.base_mem
        (setupY.isSpace V) (setupY.isDecent V))]
    [∀ (V : IntegralClosedSubspace D.site D.base D.base_mem X)
      (P : PrimeDivisor D.site D.base D.base_mem V.subspace.toFunctor),
      IsLocalRing ↥(P.genericHenselianLocalRing D.site D.base D.base_mem
        (setupX.isSpace V) (setupX.isDecent V))]
    (chernY : FirstChernComponentCycleRule D sY k)
    (chernX : FirstChernComponentCycleRule D sX (k + (r : ℤ)))
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (hW : deltaDimension D sY W = k + 1) where
  /-- The sheaf `ℒ|_W` on `W`. -/
  sheaf : Modules.{u, u} D.site D.base D.base_mem W.subspace.toFunctor (setupY.isSpace W)
  /-- The nonzero meromorphic section `s` of `ℒ|_W` the source chooses. -/
  sect : MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
    (setupY.isSpace W) sheaf
  /-- The generators of `ℒ|_W` at the generic points of the prime divisors of `W`, read off as
  the ratios they assign. -/
  ratio : LocalRatioFamily.{u, u} D.site D.base D.base_mem (setupY.isSpace W)
    (setupY.isDecent W) sheaf
  /-- **Stacks 0EQE.** The component cycle at `W` is the Weil divisor of `s`. -/
  presentation : IsDivisorPresentation sY k setupY W (chernY W hW) sheaf sect ratio
  /-- The inverse image `f^{-1}(W)`, assumed integral. -/
  preimage : IntegralClosedSubspace D.site D.base D.base_mem X
  /-- **Stacks 0EP5.** The inverse image has δ-dimension `k + r + 1`. -/
  deltaDimension_preimage : deltaDimension D sX preimage = k + (r : ℤ) + 1
  /-- The inverse image lies over `W`. -/
  preimage_points : ∀ x ∈ subspacePointSet D.site D.base D.base_mem X preimage.subspace,
    pointsMap D.site D.base D.base_mem X f x ∈
      subspacePointSet D.site D.base D.base_mem Y W.subspace
  /-- **Stacks 0EP8.** `f^*[W]` is the cycle of the inverse image, which is integral of
  multiplicity one. -/
  mult_preimage : pb.mult W preimage = 1
  /-- **Stacks 0EP8.** No other integral closed subspace occurs in `f^*[W]`. -/
  mult_eq_zero_of_ne : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem X,
    V ≠ preimage → pb.mult W V = 0
  /-- The sheaf `f^*ℒ` restricted to the inverse image. -/
  sheaf' : Modules.{u, u} D.site D.base D.base_mem preimage.subspace.toFunctor
    (setupX.isSpace preimage)
  /-- The pullback `f^*s` of the chosen section. -/
  sect' : MeromorphicSection.{u, u} D.site D.base D.base_mem preimage.subspace.toFunctor
    (setupX.isSpace preimage) sheaf'
  /-- The generators of `f^*ℒ` at the generic points of the prime divisors of the inverse
  image. -/
  ratio' : LocalRatioFamily.{u, u} D.site D.base D.base_mem (setupX.isSpace preimage)
    (setupX.isDecent preimage) sheaf'
  /-- **Stacks 0EQE.** The component cycle at the inverse image is the Weil divisor of
  `f^*s`. -/
  presentation' : IsDivisorPresentation sX (k + (r : ℤ)) setupX preimage
    (chernX preimage deltaDimension_preimage) sheaf' sect' ratio'
  /-- The prime divisor of `W` beneath a prime divisor of the inverse image. -/
  base : PrimeDivisor D.site D.base D.base_mem preimage.subspace.toFunctor →
    PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor
  /-- The multiplicity of a prime divisor of the inverse image over the prime divisor beneath
  it. -/
  multiplicity : PrimeDivisor D.site D.base D.base_mem preimage.subspace.toFunctor → ℕ
  /-- The map of henselian local rings at the generic points induced by `f`. -/
  hom : ∀ T : PrimeDivisor D.site D.base D.base_mem preimage.subspace.toFunctor,
    ↥((base T).genericHenselianLocalRing D.site D.base D.base_mem (setupY.isSpace W)
        (setupY.isDecent W)) →+*
      ↥(T.genericHenselianLocalRing D.site D.base D.base_mem (setupX.isSpace preimage)
        (setupX.isDecent preimage))
  /-- That map is local. -/
  isLocalHom : ∀ T, IsLocalHom (hom T)
  /-- That map is flat, `f` being flat. -/
  flat : ∀ T, (hom T).Flat
  /-- **Stacks 0EE9 along a flat morphism.** The multiplicity is the colength of the extended
  maximal ideal. -/
  colength : ∀ T, primeDivisorFlatMultiplicity.{u} D.site D.base D.base_mem
      (setupX.isSpace preimage) (setupX.isDecent preimage) T (setupY.isSpace W)
      (setupY.isDecent W) (base T) (hom T) = (multiplicity T : ℕ∞)
  /-- The numerator of the ratio of `s` at the generic point of the prime divisor beneath. -/
  num : ∀ T, nonZeroDivisors ↥((base T).genericHenselianLocalRing D.site D.base D.base_mem
    (setupY.isSpace W) (setupY.isDecent W))
  /-- The denominator of that ratio. -/
  den : ∀ T, nonZeroDivisors ↥((base T).genericHenselianLocalRing D.site D.base D.base_mem
    (setupY.isSpace W) (setupY.isDecent W))
  /-- The ratio of `s` at the generic point of the prime divisor beneath is that fraction. -/
  ratio_base : ∀ T, ((ratio (base T)) sect :
      (base T).genericTotalFractionRing D.site D.base D.base_mem (setupY.isSpace W)
        (setupY.isDecent W)) =
    IsLocalization.mk' ((base T).genericTotalFractionRing D.site D.base D.base_mem
      (setupY.isSpace W) (setupY.isDecent W))
      ((num T : ↥((base T).genericHenselianLocalRing D.site D.base D.base_mem
        (setupY.isSpace W) (setupY.isDecent W)))) (den T)
  /-- **Stacks 0ENC.** The ratio of `f^*s` at the generic point of `T` is the image of that
  fraction under `hom T`. -/
  ratio_preimage : ∀ T, ((ratio' T) sect' :
      T.genericTotalFractionRing D.site D.base D.base_mem (setupX.isSpace preimage)
        (setupX.isDecent preimage)) =
    IsLocalization.mk' (T.genericTotalFractionRing D.site D.base D.base_mem
        (setupX.isSpace preimage) (setupX.isDecent preimage))
      (hom T (num T : ↥((base T).genericHenselianLocalRing D.site D.base D.base_mem
        (setupY.isSpace W) (setupY.isDecent W))))
      (⟨hom T (den T : ↥((base T).genericHenselianLocalRing D.site D.base D.base_mem
          (setupY.isSpace W) (setupY.isDecent W))),
        Ring.map_mem_nonZeroDivisors_of_flatHom (flat T) (den T).2⟩ :
        nonZeroDivisors ↥(T.genericHenselianLocalRing D.site D.base D.base_mem
          (setupX.isSpace preimage) (setupX.isDecent preimage)))
  /-- **Stacks 0EP8.** The multiplicity the flat pullback attaches to `T` in `f^*[base T]`. -/
  pullbackMult : ∀ T, pb.mult
      (integralClosedSubspaceImage D sY hY W ((base T).toIntegralClosedSubspace
        D.site D.base D.base_mem))
      (integralClosedSubspaceImage D sX hX preimage (T.toIntegralClosedSubspace
        D.site D.base D.base_mem)) = (multiplicity T : ℤ)
  /-- **Stacks 0EP8.** The cycle `f^*[P]` of a prime divisor `P` of `W` is carried by the prime
  divisors of the inverse image lying over `P`. -/
  pullbackMult_eq_zero : ∀ (P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor)
      (T : IntegralClosedSubspace D.site D.base D.base_mem X),
    (∀ T' : PrimeDivisor D.site D.base D.base_mem preimage.subspace.toFunctor,
      ¬(integralClosedSubspaceImage D sX hX preimage
        (T'.toIntegralClosedSubspace D.site D.base D.base_mem) = T ∧ base T' = P)) →
    pb.mult (integralClosedSubspaceImage D sY hY W
      (P.toIntegralClosedSubspace D.site D.base D.base_mem)) T = 0

end Comparison

/-! ### Stacks 0EQR at one integral closed subspace -/

section Core

variable {D : BaseSpaceDimensionSituation.{u}}
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {sX : X ⟶ D.space} {hX : D.IsGood sX} {sY : Y ⟶ D.space} {hY : D.IsGood sY}
    {f : X ⟶ Y} {r : ℕ} {k : ℤ} {pb : FlatCyclePullback D sX hX sY hY f r}
    {setupY : SubspaceDivisorSetup D Y} {setupX : SubspaceDivisorSetup D X}
    [instY : ∀ (V : IntegralClosedSubspace D.site D.base D.base_mem Y)
      (P : PrimeDivisor D.site D.base D.base_mem V.subspace.toFunctor),
      IsLocalRing ↥(P.genericHenselianLocalRing D.site D.base D.base_mem
        (setupY.isSpace V) (setupY.isDecent V))]
    [instX : ∀ (V : IntegralClosedSubspace D.site D.base D.base_mem X)
      (P : PrimeDivisor D.site D.base D.base_mem V.subspace.toFunctor),
      IsLocalRing ↥(P.genericHenselianLocalRing D.site D.base D.base_mem
        (setupX.isSpace V) (setupX.isDecent V))]
    {chernY : FirstChernComponentCycleRule D sY k}
    {chernX : FirstChernComponentCycleRule D sX (k + (r : ℤ))}

/-- **The pointwise Stacks 0EQQ at a prime divisor of the inverse image.** The order of
vanishing of the pulled-back section along a prime divisor `T` of `f^{-1}(W)` is the multiplicity
of `T` times the order of vanishing of `s` along the prime divisor of `W` beneath `T`.

This is `AlgebraicGeometry.Space.orderOfVanishingSection_eq_multiplicity_mul`,
supplied with the comparison datum. -/
theorem FlatChernDivisorComparison.sectionOrder_eq
    {W : IntegralClosedSubspace D.site D.base D.base_mem Y}
    {hW : deltaDimension D sY W = k + 1}
    (cmp : FlatChernDivisorComparison D sX hX sY hY f r k pb setupY setupX chernY chernX W hW)
    (T : PrimeDivisor D.site D.base D.base_mem cmp.preimage.subspace.toFunctor) :
    setupX.sectionOrder cmp.preimage cmp.sheaf' cmp.sect' cmp.ratio' T =
      (cmp.multiplicity T : ℤ) *
        setupY.sectionOrder W cmp.sheaf cmp.sect cmp.ratio (cmp.base T) := by
  have := setupX.noetherian cmp.preimage
  have := setupX.krullDimLE cmp.preimage
  have := setupY.noetherian W
  have := setupY.krullDimLE W
  exact orderOfVanishingSection_eq_multiplicity_mul.{u, u} D.site D.base D.base_mem
    (setupX.isSpace cmp.preimage) (setupX.isDecent cmp.preimage) T
    (setupY.isSpace W) (setupY.isDecent W) (cmp.base T)
    (cmp.isLocalHom T) (cmp.flat T) (cmp.colength T) cmp.sheaf cmp.sheaf' cmp.sect cmp.sect'
    (cmp.ratio (cmp.base T)) (cmp.ratio' T) (cmp.num T) (cmp.den T)
    (cmp.ratio_base T) (cmp.ratio_preimage T)

/-- **Stacks 0EQR at a single integral closed subspace.** For an integral closed subspace
`W ⊆ Y` of δ-dimension `k + 1` with integral inverse image, the coefficient at `T ⊆ X` of the
flat pullback of the component cycle of `W` equals the coefficient at `T` of the component cycle
of `f^{-1}(W)`, weighted by the multiplicity with which `f^{-1}(W)` occurs in `f^*[W]`.

Both sides collapse to a single term, and the two terms are equal by the pointwise Stacks
0EQQ. -/
theorem flatCyclePullback_mult_firstChernComponentCycle
    {W : IntegralClosedSubspace D.site D.base D.base_mem Y}
    {hW : deltaDimension D sY W = k + 1}
    (cmp : FlatChernDivisorComparison D sX hX sY hY f r k pb setupY setupX chernY chernX W hW)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (∑ᶠ Z : IntegralClosedSubspace D.site D.base D.base_mem Y,
        (firstChernComponentCycle D sY hY k chernY W).1 Z * pb.mult Z T) =
      ∑ᶠ V : IntegralClosedSubspace D.site D.base D.base_mem X,
        pb.mult W V *
          (firstChernComponentCycle D sX hX (k + (r : ℤ)) chernX V).1 T := by
  have hright : (∑ᶠ V : IntegralClosedSubspace D.site D.base D.base_mem X,
      pb.mult W V * (firstChernComponentCycle D sX hX (k + (r : ℤ)) chernX V).1 T) =
      (firstChernComponentCycle D sX hX (k + (r : ℤ)) chernX cmp.preimage).1 T := by
    rw [finsum_eq_single _ cmp.preimage fun V hV => by
      rw [cmp.mult_eq_zero_of_ne V hV, zero_mul], cmp.mult_preimage, one_mul]
  have hterm : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem Y,
      (∀ P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor,
        integralClosedSubspaceImage D sY hY W
          (P.toIntegralClosedSubspace D.site D.base D.base_mem) = Z → pb.mult Z T = 0) →
      (firstChernComponentCycle D sY hY k chernY W).1 Z * pb.mult Z T = 0 := by
    intro Z hZ
    by_cases himZ : ∃ Z' : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor,
        integralClosedSubspaceImage D sY hY W Z' = Z
    · obtain ⟨Z', rfl⟩ := himZ
      by_cases hpd : ∃ P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor,
          P.toIntegralClosedSubspace D.site D.base D.base_mem = Z'
      · obtain ⟨P, rfl⟩ := hpd
        rw [hZ P rfl, mul_zero]
      · rw [firstChernComponentCycle_apply_image D sY hY W k chernY hW,
          cmp.presentation.coeff_eq_zero Z' fun P hP => hpd ⟨P, hP⟩, zero_mul]
    · rw [firstChernComponentCycle_apply_eq_zero_of_forall_ne D sY hY W k chernY Z
        fun Z' hZ' => himZ ⟨Z', hZ'⟩, zero_mul]
  rw [hright]
  by_cases hex : ∃ T' : PrimeDivisor D.site D.base D.base_mem cmp.preimage.subspace.toFunctor,
      integralClosedSubspaceImage D sX hX cmp.preimage
        (T'.toIntegralClosedSubspace D.site D.base D.base_mem) = T
  · obtain ⟨T', rfl⟩ := hex
    rw [firstChernComponentCycle_apply_image D sX hX cmp.preimage (k + (r : ℤ)) chernX
        cmp.deltaDimension_preimage, cmp.presentation'.coeff_primeDivisor T',
      finsum_eq_single _ (integralClosedSubspaceImage D sY hY W
        ((cmp.base T').toIntegralClosedSubspace D.site D.base D.base_mem)) ?_,
      firstChernComponentCycle_apply_image D sY hY W k chernY hW,
      cmp.presentation.coeff_primeDivisor (cmp.base T'), cmp.pullbackMult T',
      cmp.sectionOrder_eq T', mul_comm]
    intro Z hZ
    refine hterm Z fun P hP => ?_
    have hne : P ≠ cmp.base T' := by
      rintro rfl
      exact hZ hP.symm
    rw [← hP, cmp.pullbackMult_eq_zero P _ ?_]
    rintro T'' ⟨himT, hbase⟩
    have hT'' : T'' = T' :=
      PrimeDivisor.injective_toIntegralClosedSubspace D.site D.base D.base_mem
        (injective_integralClosedSubspaceImage D sX hX cmp.preimage himT)
    exact hne (by rw [← hbase, hT''])
  · have hzero : (firstChernComponentCycle D sX hX (k + (r : ℤ)) chernX cmp.preimage).1 T = 0 := by
      by_cases himT : ∃ V' : IntegralClosedSubspace D.site D.base D.base_mem
          cmp.preimage.subspace.toFunctor, integralClosedSubspaceImage D sX hX cmp.preimage V' = T
      · obtain ⟨V', rfl⟩ := himT
        rw [firstChernComponentCycle_apply_image D sX hX cmp.preimage (k + (r : ℤ)) chernX
          cmp.deltaDimension_preimage,
          cmp.presentation'.coeff_eq_zero V' fun T' hT' => hex ⟨T', by rw [hT']⟩]
      · exact firstChernComponentCycle_apply_eq_zero_of_forall_ne D sX hX cmp.preimage
          (k + (r : ℤ)) chernX T fun V' hV' => himT ⟨V', hV'⟩
    rw [hzero]
    refine finsum_eq_zero_of_forall_eq_zero fun Z => hterm Z fun P hP => ?_
    rw [← hP, cmp.pullbackMult_eq_zero P T fun T' hT' => hex ⟨T', hT'.1⟩]

/-- Away from δ-dimension `k + 1` the comparison is between two zeros: the component cycle of
`W` vanishes, and a subspace with a nonzero multiplicity in `f^{-1}(W)` has δ-dimension
`dim_δ(W) + r`, which is not the δ-dimension at which the component rule on `X` is nonzero. -/
theorem mult_mul_firstChernComponentCycle_eq_zero
    {W : IntegralClosedSubspace D.site D.base D.base_mem Y}
    (hW : deltaDimension D sY W ≠ k + 1)
    (V : IntegralClosedSubspace D.site D.base D.base_mem X)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X) :
    pb.mult W V * (firstChernComponentCycle D sX hX (k + (r : ℤ)) chernX V).1 T = 0 := by
  by_cases hm : pb.mult W V = 0
  · rw [hm, zero_mul]
  by_cases hc : (firstChernComponentCycle D sX hX (k + (r : ℤ)) chernX V).1 T = 0
  · rw [hc, mul_zero]
  refine absurd ?_ hW
  have hV : deltaDimension D sX V = k + (r : ℤ) + 1 := by
    by_contra hne
    rw [firstChernComponentCycle_of_deltaDimension_ne D sX hX (k + (r : ℤ)) chernX hne] at hc
    exact hc rfl
  have hd := pb.deltaDimension_eq_of_mult_ne_zero W V hm
  rw [hV] at hd
  omega

/-- **Stacks 0EQR at a single integral closed subspace, with no restriction on its
δ-dimension.** -/
theorem flatCyclePullback_mult_firstChernComponentCycle_of_forall
    (cmp : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
      (hW : deltaDimension D sY W = k + 1),
      FlatChernDivisorComparison D sX hX sY hY f r k pb setupY setupX chernY chernX W hW)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (∑ᶠ Z : IntegralClosedSubspace D.site D.base D.base_mem Y,
        (firstChernComponentCycle D sY hY k chernY W).1 Z * pb.mult Z T) =
      ∑ᶠ V : IntegralClosedSubspace D.site D.base D.base_mem X,
        pb.mult W V *
          (firstChernComponentCycle D sX hX (k + (r : ℤ)) chernX V).1 T := by
  by_cases hW : deltaDimension D sY W = k + 1
  · exact flatCyclePullback_mult_firstChernComponentCycle (cmp W hW) T
  · refine (finsum_eq_zero_of_forall_eq_zero fun Z => ?_).trans
      (finsum_eq_zero_of_forall_eq_zero fun V =>
        mult_mul_firstChernComponentCycle_eq_zero hW V T).symm
    rw [firstChernComponentCycle_of_deltaDimension_ne D sY hY k chernY hW]
    have hz : (0 : CycleGroup D sY k).1 Z = 0 := rfl
    rw [hz, zero_mul]

end Core

/-! ### Stacks 0EQR

The passage from a single integral closed subspace to an arbitrary cycle exchanges two
locally finite double sums.  The two finiteness statements it needs are isolated first. -/

section Main

variable {D : BaseSpaceDimensionSituation.{u}}
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {sX : X ⟶ D.space} {hX : D.IsGood sX} {sY : Y ⟶ D.space} {hY : D.IsGood sY}
    {f : X ⟶ Y} {r : ℕ} {k : ℤ} {pb : FlatCyclePullback D sX hX sY hY f r}
    {setupY : SubspaceDivisorSetup D Y} {setupX : SubspaceDivisorSetup D X}
    [instY : ∀ (V : IntegralClosedSubspace D.site D.base D.base_mem Y)
      (P : PrimeDivisor D.site D.base D.base_mem V.subspace.toFunctor),
      IsLocalRing ↥(P.genericHenselianLocalRing D.site D.base D.base_mem
        (setupY.isSpace V) (setupY.isDecent V))]
    [instX : ∀ (V : IntegralClosedSubspace D.site D.base D.base_mem X)
      (P : PrimeDivisor D.site D.base D.base_mem V.subspace.toFunctor),
      IsLocalRing ↥(P.genericHenselianLocalRing D.site D.base D.base_mem
        (setupX.isSpace V) (setupX.isDecent V))]
    {chernY : FirstChernComponentCycleRule D sY k}
    {chernX : FirstChernComponentCycleRule D sX (k + (r : ℤ))}
    (α : CycleGroup D sY (k + 1))
    (T : IntegralClosedSubspace D.site D.base D.base_mem X)

/-- The subspaces occurring in a cycle `β` on `Y` through a given point form a finite set: the
subspaces occurring in a cycle are locally finite. -/
private theorem finite_subspaces_through_point {m : ℤ} (β : CycleGroup D sY m)
    (p : points D.site D.base D.base_mem Y) :
    {W : IntegralClosedSubspace D.site D.base D.base_mem Y | β.1 W ≠ 0 ∧
      p ∈ subspacePointSet D.site D.base D.base_mem Y W.subspace}.Finite := by
  obtain ⟨V, hV, hVfin⟩ := β.2.1 p
  refine hVfin.subset ?_
  rintro W ⟨hWne, hWp⟩
  exact ⟨_, by simpa [hWne] using hWp, mem_of_mem_nhds hV⟩

/-- The subspaces occurring in `α` through the image of the generic point of `T` form a finite
set: the subspaces occurring in a cycle are locally finite. -/
private theorem finite_subspaces_through_image :
    {W : IntegralClosedSubspace D.site D.base D.base_mem Y | α.1 W ≠ 0 ∧
      pointsMap D.site D.base D.base_mem X f
          (T.ambientGenericPoint D.site D.base D.base_mem) ∈
        subspacePointSet D.site D.base D.base_mem Y W.subspace}.Finite :=
  finite_subspaces_through_point α _

/-- The subspaces at which a component cycle of a subspace occurring in `α` is nonzero and which
pass through the image of the generic point of `T` form a finite set: finitely many subspaces
occur in `α` near that point, and the component cycle of each is itself a cycle. -/
private theorem finite_component_subspaces_through_image :
    {Z : IntegralClosedSubspace D.site D.base D.base_mem Y |
      (∃ W : IntegralClosedSubspace D.site D.base D.base_mem Y, α.1 W ≠ 0 ∧
          (firstChernComponentCycle D sY hY k chernY W).1 Z ≠ 0) ∧
        pointsMap D.site D.base D.base_mem X f
            (T.ambientGenericPoint D.site D.base D.base_mem) ∈
          subspacePointSet D.site D.base D.base_mem Y Z.subspace}.Finite := by
  refine ((finite_subspaces_through_image (f := f) α T).biUnion
    (t := fun W : IntegralClosedSubspace D.site D.base D.base_mem Y =>
      {Z : IntegralClosedSubspace D.site D.base D.base_mem Y |
        (firstChernComponentCycle D sY hY k chernY W).1 Z ≠ 0 ∧
          pointsMap D.site D.base D.base_mem X f
              (T.ambientGenericPoint D.site D.base D.base_mem) ∈
            subspacePointSet D.site D.base D.base_mem Y Z.subspace})
    fun W _ => finite_subspaces_through_point _ _).subset ?_
  rintro Z ⟨⟨W, hWne, hccne⟩, hZp⟩
  have hsub := subspacePointSet_subset_of_firstChernComponentCycle_ne_zero D sY hY k chernY W Z
    hccne
  exact Set.mem_biUnion (x := W) ⟨hWne, hsub hZp⟩ ⟨hccne, hZp⟩

/-- The subspaces of `X` occurring in `f^*α` with a nonzero component cycle at `T` form a finite
set: each of them is the inverse image of one of the finitely many subspaces occurring in `α`
near the image of the generic point of `T`. -/
private theorem finite_preimage_subspaces
    (cmp : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
      (hW : deltaDimension D sY W = k + 1),
      FlatChernDivisorComparison D sX hX sY hY f r k pb setupY setupX chernY chernX W hW) :
    {V : IntegralClosedSubspace D.site D.base D.base_mem X |
      ∃ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
        (α.1 W ≠ 0 ∧ pointsMap D.site D.base D.base_mem X f
            (T.ambientGenericPoint D.site D.base D.base_mem) ∈
          subspacePointSet D.site D.base D.base_mem Y W.subspace) ∧
        pb.mult W V ≠ 0 ∧
          (firstChernComponentCycle D sX hX (k + (r : ℤ)) chernX V).1 T ≠ 0}.Finite := by
  have hinner : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
      {V : IntegralClosedSubspace D.site D.base D.base_mem X | pb.mult W V ≠ 0 ∧
        (firstChernComponentCycle D sX hX (k + (r : ℤ)) chernX V).1 T ≠ 0}.Finite := by
    intro W
    by_cases hW : deltaDimension D sY W = k + 1
    · refine (Set.finite_singleton (cmp W hW).preimage).subset ?_
      rintro V ⟨hm, -⟩
      rw [Set.mem_singleton_iff]
      by_contra hne
      exact hm ((cmp W hW).mult_eq_zero_of_ne V hne)
    · refine Set.finite_empty.subset ?_
      rintro V ⟨hm, hc⟩
      exact absurd (mult_mul_firstChernComponentCycle_eq_zero hW V T)
        (mul_ne_zero hm hc)
  have hbig := (finite_subspaces_through_image (f := f) α T).biUnion
    (t := fun W : IntegralClosedSubspace D.site D.base D.base_mem Y =>
      {V : IntegralClosedSubspace D.site D.base D.base_mem X | pb.mult W V ≠ 0 ∧
        (firstChernComponentCycle D sX hX (k + (r : ℤ)) chernX V).1 T ≠ 0})
    fun W _ => hinner W
  refine hbig.subset ?_
  rintro V ⟨W, hWA, hm, hc⟩
  exact Set.mem_biUnion (x := W) hWA ⟨hm, hc⟩

variable {α T}

/-- **Stacks 0EQR, as an identity of cycles.** In Situation 0EDT let `X/B` and `Y/B` be good,
let `f : X ⟶ Y` be flat of relative dimension `r`, let `ℒ` be an invertible `O_Y`-module and let
`α` be a `(k+1)`-cycle on `Y`.  Then

  `f^*(c₁(ℒ) ∩ α) = c₁(f^*ℒ) ∩ f^*α`

in `Z_{k+r}(X)`.

The cap product is the carried Stacks 0EQJ at the level of cycles,
`AlgebraicGeometry.Space.firstChernCapCycleMap`, whose component rule is an explicit parameter;
the flat pullback is the carried Stacks 0EP8, whose defining formula is the field
`AlgebraicGeometry.Space.FlatCyclePullback.coeff`.  The identity of cycles is finer than the
source's identity of classes in `CH_{k+r-1}(X)`, which it implies; see
`AlgebraicGeometry.Space.flatPullback_firstChernClassCap`.

Nothing about either side of the equality is assumed.  At a single integral closed subspace the
identity is `AlgebraicGeometry.Space.flatCyclePullback_mult_firstChernComponentCycle`, whose
content is the pointwise Stacks 0EQQ; the passage to a general cycle exchanges two locally
finite double sums, which is the bookkeeping the source performs through Remark 0EQ8. -/
@[stacks 0EQR "as an identity of cycles in Z_{k+r}(X) rather than of classes in CH, which is the
finer statement and implies the source's once the class maps are known compatible — see
flatPullback_firstChernClassCap, which states the source's own grading. The cap product is the
cap product of Stacks 0EQJ as carried in this repository, firstChernCapCycleMap, so the
component cycle c_1(L|_W) ∩ [W] remains an explicit parameter standing in for Stacks 0EQE, which
does not exist for algebraic spaces here. PROVED, not assumed: the commutation itself. At a
single integral closed subspace W both coefficients collapse to one term and those terms are
equal by the pointwise Stacks 0EQQ
(orderOfVanishingSection_eq_multiplicity_mul); the passage to a general cycle is the
locally finite bookkeeping the source performs by appealing to Remark 0EQ8, and it is carried
out here by exchanging two double sums. No additive map is assumed to commute with the cap
product and no conjunct of the conclusion is a hypothesis. RESTRICTED: carried as explicit named
hypotheses are (i) the flat pullback of cycles of Stacks 0EP8, which this repository does not
construct, carried as FlatCyclePullback, that is TOGETHER WITH
ITS DEFINING FORMULA: a multiplicity mult W T for each pair of integral closed subspaces, the
maps Z_m(Y) → Z_n(X) for m + r = n, the statement that the coefficient of f^*α at T is
∑ α_W · mult W T, and that f^*[W] is carried by f^{-1}(W); (ii) the Weil divisor presentations of
Stacks 0EQE for the two component rules, exactly as Stacks 0EQK carries them, with
the sheaves L|_W and f^*L|_{f^{-1}(W)} and the sections s and f^*s as unconstrained parameters
identified by their ratios at the generic points, as in the carried Stacks 0EQQ, this repository
having no pullback of a sheaf of modules or of a meromorphic section along a morphism of
algebraic spaces; (iii) at each prime divisor of f^{-1}(W) the flat local homomorphism of
henselian local rings over the prime divisor of W beneath it, with its locality and flatness, as
in the carried Stacks 0EQA and 0EQQ; and (iv) the identification of the multiplicity Stacks 0EP8
attaches to that prime divisor with the colength primeDivisorFlatMultiplicity, which is Stacks
0EE9 read along a flat morphism and is not proved here. The inverse image of each integral
closed subspace occurring in α is assumed INTEGRAL, which is the case i = 1, n_1 = 1 of the
source's sum over the irreducible components of f^{-1}(W); the step to several components is the
additivity over them of the multiplicities of Stacks 0EE2 and Stacks 0EE9, which is NOT
COVERED by Stacks 0EQA and 0EQQ as stated here, and it is NOT COVERED here either"]
theorem flatCyclePullback_firstChernCapCycleMap
    (_hflat : IsFlat D.site D.base D.base_mem f)
    (_hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (cmp : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
      (hW : deltaDimension D sY W = k + 1),
      FlatChernDivisorComparison D sX hX sY hY f r k pb setupY setupX chernY chernX W hW)
    (α : CycleGroup D sY (k + 1)) :
    pb.map k (k + (r : ℤ)) rfl (firstChernCapCycleMap D sY hY k chernY α) =
      firstChernCapCycleMap D sX hX (k + (r : ℤ)) chernX
        (pb.map (k + 1) (k + (r : ℤ) + 1) (by ring) α) := by
  refine Subtype.ext (funext fun T => ?_)
  have hL : (pb.map k (k + (r : ℤ)) rfl (firstChernCapCycleMap D sY hY k chernY α)).1 T =
      ∑ᶠ Z : IntegralClosedSubspace D.site D.base D.base_mem Y,
        ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
          α.1 W * (firstChernComponentCycle D sY hY k chernY W).1 Z * pb.mult Z T := by
    rw [pb.coeff]
    exact finsum_congr fun Z => by rw [firstChernCapCycleMap_apply, finsum_mul]
  have hR : (firstChernCapCycleMap D sX hX (k + (r : ℤ)) chernX
        (pb.map (k + 1) (k + (r : ℤ) + 1) (by ring) α)).1 T =
      ∑ᶠ V : IntegralClosedSubspace D.site D.base D.base_mem X,
        ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
          α.1 W * pb.mult W V *
            (firstChernComponentCycle D sX hX (k + (r : ℤ)) chernX V).1 T := by
    rw [firstChernCapCycleMap_apply]
    exact finsum_congr fun V => by rw [pb.coeff, finsum_mul]
  have hvanL : ∀ (Z W : IntegralClosedSubspace D.site D.base D.base_mem Y),
      α.1 W * (firstChernComponentCycle D sY hY k chernY W).1 Z * pb.mult Z T ≠ 0 →
      Z ∈ {Z : IntegralClosedSubspace D.site D.base D.base_mem Y |
          (∃ W' : IntegralClosedSubspace D.site D.base D.base_mem Y, α.1 W' ≠ 0 ∧
              (firstChernComponentCycle D sY hY k chernY W').1 Z ≠ 0) ∧
            pointsMap D.site D.base D.base_mem X f
                (T.ambientGenericPoint D.site D.base D.base_mem) ∈
              subspacePointSet D.site D.base D.base_mem Y Z.subspace} ∧
        W ∈ {W : IntegralClosedSubspace D.site D.base D.base_mem Y | α.1 W ≠ 0 ∧
          pointsMap D.site D.base D.base_mem X f
              (T.ambientGenericPoint D.site D.base D.base_mem) ∈
            subspacePointSet D.site D.base D.base_mem Y W.subspace} := by
    intro Z W hZW
    have hαW : α.1 W ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hZW)
    have hccZ : (firstChernComponentCycle D sY hY k chernY W).1 Z ≠ 0 :=
      right_ne_zero_of_mul (left_ne_zero_of_mul hZW)
    have hpZ := pb.mult_support Z T (right_ne_zero_of_mul hZW)
    exact ⟨⟨⟨W, hαW, hccZ⟩, hpZ⟩,
      ⟨hαW, subspacePointSet_subset_of_firstChernComponentCycle_ne_zero D sY hY k chernY W Z
        hccZ hpZ⟩⟩
  have hvanR : ∀ (V : IntegralClosedSubspace D.site D.base D.base_mem X)
      (W : IntegralClosedSubspace D.site D.base D.base_mem Y),
      α.1 W * pb.mult W V *
          (firstChernComponentCycle D sX hX (k + (r : ℤ)) chernX V).1 T ≠ 0 →
      V ∈ {V : IntegralClosedSubspace D.site D.base D.base_mem X |
          ∃ W' : IntegralClosedSubspace D.site D.base D.base_mem Y,
            (α.1 W' ≠ 0 ∧ pointsMap D.site D.base D.base_mem X f
                (T.ambientGenericPoint D.site D.base D.base_mem) ∈
              subspacePointSet D.site D.base D.base_mem Y W'.subspace) ∧
            pb.mult W' V ≠ 0 ∧
              (firstChernComponentCycle D sX hX (k + (r : ℤ)) chernX V).1 T ≠ 0} ∧
        W ∈ {W : IntegralClosedSubspace D.site D.base D.base_mem Y | α.1 W ≠ 0 ∧
          pointsMap D.site D.base D.base_mem X f
              (T.ambientGenericPoint D.site D.base D.base_mem) ∈
            subspacePointSet D.site D.base D.base_mem Y W.subspace} := by
    intro V W hVW
    have hαW : α.1 W ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hVW)
    have hmV : pb.mult W V ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hVW)
    have hccV : (firstChernComponentCycle D sX hX (k + (r : ℤ)) chernX V).1 T ≠ 0 :=
      right_ne_zero_of_mul hVW
    have hW : deltaDimension D sY W = k + 1 := by
      by_contra hne
      exact absurd (mult_mul_firstChernComponentCycle_eq_zero hne V T)
        (mul_ne_zero hmV hccV)
    have hVeq : V = (cmp W hW).preimage := by
      by_contra hne
      exact hmV ((cmp W hW).mult_eq_zero_of_ne V hne)
    have hTV : T.ambientGenericPoint D.site D.base D.base_mem ∈
        subspacePointSet D.site D.base D.base_mem X V.subspace :=
      subspacePointSet_subset_of_firstChernComponentCycle_ne_zero D sX hX (k + (r : ℤ)) chernX
        V T hccV ⟨T.genericPoint D.site D.base D.base_mem, rfl⟩
    have hpW := (cmp W hW).preimage_points _ (by rw [hVeq] at hTV; exact hTV)
    exact ⟨⟨W, ⟨hαW, hpW⟩, hmV, hccV⟩, ⟨hαW, hpW⟩⟩
  rw [hL, hR,
    finsum_exchange_of_vanishing _ (finite_component_subspaces_through_image α T)
      (finite_subspaces_through_image (f := f) α T) hvanL,
    finsum_exchange_of_vanishing _ (finite_preimage_subspaces α T cmp)
      (finite_subspaces_through_image (f := f) α T) hvanR]
  refine finsum_congr fun W => ?_
  rw [finsum_congr fun Z => mul_assoc (α.1 W)
      ((firstChernComponentCycle D sY hY k chernY W).1 Z) (pb.mult Z T),
    ← mul_finsum, finsum_congr fun V => mul_assoc (α.1 W) (pb.mult W V)
      ((firstChernComponentCycle D sX hX (k + (r : ℤ)) chernX V).1 T),
    ← mul_finsum, flatCyclePullback_mult_firstChernComponentCycle_of_forall cmp W T]

/-- **Stacks 0EQR.** In Situation 0EDT let `X/B` and `Y/B` be good, let `f : X ⟶ Y` be flat of
relative dimension `r`, let `ℒ` be an invertible `O_Y`-module and let `α` be a `(k+1)`-cycle on
`Y`.  Then

  `f^*(c₁(ℒ) ∩ α) = c₁(f^*ℒ) ∩ f^*α`

in `CH_{k+r}(X)`, for the cap product of Stacks 0EQJ as carried in this repository.

This is `AlgebraicGeometry.Space.flatCyclePullback_firstChernCapCycleMap` composed with the class
maps of the two Chow groups.  The flat pullback on Chow groups is the parameter `fstarCH`, and
all that is asked of it is that it be induced by the flat pullback of cycles, which is the
content of Stacks 0EQ9 — that flat pullback respects rational equivalence — and is the
hypothesis `hclass`.  That hypothesis says nothing about the cap product. -/
@[stacks 0EQR "the source's own grading: f^*(c_1(L) ∩ α) = c_1(f^*L) ∩ f^*α in the Chow groups,
for the cap product of Stacks 0EQJ as carried here, so the component cycle c_1(L|_W) ∩ [W] and
the Chow groups CH of Stacks 0EQ6 remain explicit parameters, standing in for Stacks 0EQE and
Stacks 0EQ6 parts (2)-(4). PROVED, not assumed: the commutation, which is
flatCyclePullback_firstChernCapCycleMap — the identity of cycles whose content is the
pointwise Stacks 0EQQ — read through the two class maps. RESTRICTED: in addition to the
hypotheses of flatCyclePullback_firstChernCapCycleMap, which are listed on it (the flat pullback
of cycles of Stacks 0EP8 with its defining formula; the Weil divisor
presentations of Stacks 0EQE; the flat local homomorphisms of henselian local rings; the
identification of the multiplicity of Stacks 0EP8 with the colength; and the inverse image of
each integral closed subspace occurring in α assumed integral), the flat pullback on the Chow
groups is the parameter fstarCH together with hclass, that it is induced by the flat pullback of
cycles — which is Stacks 0EQ9, that flat pullback respects rational equivalence, and says
nothing about the cap product. The invertible sheaves L on Y and N on X, the latter standing for
f^*L, are unconstrained parameters as they are in the carried Stacks 0EQQ and as they are for
firstChernClassCap itself, which does not consume them"]
theorem flatPullback_firstChernClassCap
    (_hflat : IsFlat D.site D.base D.base_mem f)
    (_hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (cmp : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
      (hW : deltaDimension D sY W = k + 1),
      FlatChernDivisorComparison D sX hX sY hY f r k pb setupY setupX chernY chernX W hW)
    (L : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hL : IsInvertibleSheaf D sY hY L)
    (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleSheaf D sX hX N)
    {CHY : Type w} [AddCommGroup CHY] (chowY : ChowTarget.{u, w, v} D sY hY k CHY)
    {CHX : Type w} [AddCommGroup CHX]
    (chowX : ChowTarget.{u, w, v} D sX hX (k + (r : ℤ)) CHX)
    (fstarCH : CHY →+ CHX)
    (hclass : ∀ β : CycleGroup D sY k,
      chowX.cls (pb.map k (k + (r : ℤ)) rfl β) = fstarCH (chowY.cls β))
    (α : CycleGroup D sY (k + 1)) :
    fstarCH (firstChernClassCap D sY hY L k hL chernY chowY α) =
      firstChernClassCap D sX hX N (k + (r : ℤ)) hN chernX chowX
        (pb.map (k + 1) (k + (r : ℤ) + 1) (by ring) α) := by
  rw [firstChernClassCap, firstChernClassCap, AddMonoidHom.comp_apply,
    AddMonoidHom.comp_apply, ← hclass,
    flatCyclePullback_firstChernCapCycleMap _hflat _hr cmp α]

end Main

end AlgebraicGeometry.Space

end

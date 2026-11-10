module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ExteriorProductCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductProjections

/-!
# The exterior product with a fundamental class is the cap product of a bivariant class

Let `(S, δ)` be a base situation whose base is the spectrum of a field, so that the exterior
product of Stacks 0FBV is available, let `X` be an **integral** scheme locally of finite type and
flat over `S` of relative dimension `d`, and let `[X] ∈ CH_d(X)` be its fundamental class. Then

  `[X] × - : CH_k(T) ⟶ CH_{d+k}(X ×_S T)`

is the cap operation of a bivariant class in `A^{-d}(X ⟶ S)`, namely of the flat-pullback class
of **Stacks 0B78** for the structure morphism of `X`. This is
`Stacks.Chow.IsExteriorProductBivariantClass` — Stacks 0FBW in its exterior-product form — for
the fundamental class of `X`.

## Main results

* `Stacks.Chow.chowGroupDegreeEquiv_flatPullbackChowSnd_eq_chowExteriorProduct` — **clause (1) of
  Stacks 0B0R on Chow groups**, second projection: the flat pullback of a class `c ∈ CH_k(T)`
  along `pr_T : X ×_S T ⟶ T` is the exterior product `[X] × c`. The existing carrier
  `Stacks.Chow.flatPullbackSnd_eq_fundamentalCycle_exteriorProduct` states this on cycles; this is
  the same statement read modulo rational equivalence, which is the form the conditions of Stacks
  0B76 are stated in.
* `Stacks.Chow.isExteriorProductBivariantClass_flatPullbackBivariantClass` — **Stacks 0FBW in its
  exterior-product form for the fundamental class of an integral scheme**: the class of Stacks
  0B78 for the structure morphism of `X` caps as the exterior product with `[X]`.

## Implementation notes

### Why no condition of Stacks 0B76 has to be proved for the exterior product

The implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ExteriorProductCommuting` observe that building a
term of `Stacks.Chow.BivariantClass` whose cap operation is `γ ↦ α × γ` requires the three
conditions of Stacks 0B76 for the exterior product, and that the third of them — compatibility
with the Gysin map — cannot be derived at all, the Gysin map of a `Stacks.Chow.GysinSystem` being
abstract data.

Nothing below builds such a term. The class exhibited here is the one Stacks 0B78 already
delivers, `Stacks.Chow.flatPullbackBivariantClass` for the structure morphism of `X`, all three of
whose conditions are discharged where that class is constructed; what is proved here is that its
cap operation *happens to be* the exterior product with `[X]`. The compatibility with the Gysin
map is therefore inherited and not re-derived, and the obstruction those notes describe does not
arise. The identification of the two operations is clause (1) of Stacks 0B0R, which this
repository proves outright.

This covers exactly the classes `α` that are fundamental classes of integral schemes flat over
the base. It does not cover a general `α ∈ CH_n(X)`: for that the source passes to a coproduct
`∐ X_i` and uses the compatibility of the exterior product with proper pushforward in its first
variable, which — see
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ExteriorProductCommuting` — has no carrier in this
repository.

### The hypotheses carried

Three, all of them prerequisites already carried throughout this part of the library, and none of
them a part of the conclusion:

* `hfp : Stacks.Chow.FlatPullbackDescends C` is **Stacks 02S1**. Without it neither
  `Stacks.Chow.flatPullbackChow` nor `Stacks.Chow.chowExteriorProduct` exists, so it is a
  prerequisite of writing the statement down at all.
* `hRG : Stacks.Chow.ProperPushforwardFlatPullbackBaseChange C` is **Stacks 02RG** on Chow groups
  and `h71 : G.FlatPullbackNaturality d` is **Stacks 0B71** with the identification of Stacks
  0B6Y. These two are consumed only by `Stacks.Chow.flatPullbackBivariantClass`, where they
  discharge the proper-pushforward and the Gysin condition of Stacks 0B76; they are exactly the
  hypotheses of Stacks 0B78 in this repository and say nothing about the exterior product.

### Degrees

Flat pullback of relative dimension `d` sends degree `k` to `k + d`, the exterior product with a
class of degree `d` sends it to `d + k`, and a bivariant class of degree `-d` sends it to
`k - (-d)`. These are three spellings of one integer, and
`Stacks.Chow.chowGroupDegreeEquiv` mediates between them; the comparison with the cap operation
of Stacks 0B78 is a heterogeneous equality for the same reason, as everywhere in this part of the
library.

## References

* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 0B0R](https://stacks.math.columbia.edu/tag/0B0R)
* [Stacks Project, Tag 0B71](https://stacks.math.columbia.edu/tag/0B71)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 0FBV](https://stacks.math.columbia.edu/tag/0FBV)
* [Stacks Project, Tag 0FBW](https://stacks.math.columbia.edu/tag/0FBW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Transport along an equality of degrees, on the class of a cycle -/


/-! ### Clause (1) of Stacks 0B0R on Chow groups -/

/-- **Clause (1) of Stacks 0B0R on Chow groups, second projection.** Let the base be the spectrum
of a field, let `X` be integral locally of finite type over it with
`relativeDimension` of its generic point equal to `d`, let `T` be locally of finite type over the
base and let `c ∈ CH_k(T)`. Then the flat pullback of `c` along the projection
`pr_T : X ×_S T ⟶ T` is the exterior product `[X] × c` of the fundamental class of `X` with `c`,

  `pr_T^* c = [X] × c`   in   `CH_{d+k}(X ×_S T)`.

The left-hand side is produced in degree `k + d` and the right-hand side in degree `d + k`, so
the two are compared through `Stacks.Chow.chowGroupDegreeEquiv`, which is the identity on cycle
coefficients.

On the class of a cycle this is
`Stacks.Chow.flatPullbackSnd_eq_fundamentalCycle_exteriorProduct`, the existing carrier of the
same clause on cycles, read modulo rational equivalence. -/
theorem chowGroupDegreeEquiv_flatPullbackChowSnd_eq_chowExteriorProduct (C : ChowSituation.{u})
    [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
    (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
    {X T : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sT : T ⟶ C.S)
    [LocallyOfFiniteType sT] [IsIntegral X] (d : ℕ)
    (hrel : AlgebraicGeometry.RelativeDimension (pullback.snd sX sT) d)
    (hd : relativeDimension C.dimensionFunction sX (genericPoint X) = (d : ℤ)) (k : ℤ)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C (pullback.fst sX sT ≫ sX) sT
      (pullback.snd sX sT) pullback.condition.symm d hrel k)
    (c : chowGroup C sT k) :
    chowGroupDegreeEquiv C (pullback.fst sX sT ≫ sX) (add_comm k (d : ℤ))
        (flatPullbackChow C (pullback.fst sX sT ≫ sX) sT (pullback.snd sX sT)
          pullback.condition.symm d hrel k hfac c) =
      chowExteriorProduct C hδ sX sT (d : ℤ) k
        (TensorProduct.tmul ℤ (fundamentalChowClass C sX (d : ℤ)) c) := by
  induction c using QuotientAddGroup.induction_on with
  | H γ =>
    exact chowGroupDegreeEquiv_mk_eq_mk_of_val C (pullback.fst sX sT ≫ sX)
      (add_comm k (d : ℤ)) _ _
      (flatPullbackSnd_eq_fundamentalCycle_exteriorProduct C sX sT d hrel hd k γ)

/-! ### Stacks 0FBW in its exterior-product form, for a fundamental class -/

/-- **Stacks 0FBW in its exterior-product form, for the fundamental class of an integral scheme.**
Let the base be the spectrum of a field, let `X` be integral and flat over it of relative
dimension `d`, and let `[X] ∈ CH_d(X)` be its fundamental class. Then the flat-pullback bivariant
class of **Stacks 0B78** for the structure morphism of `X`, an element of `A^{-d}(X ⟶ S)`, caps as
the exterior product with `[X]`:

  `c ∩ γ = [X] × γ`   for every test `sT : T ⟶ S` and every `γ ∈ CH_k(T)`.

This is `Stacks.Chow.IsExteriorProductBivariantClass` for `α = [X]`, the predicate that
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ExteriorProductCommuting` names as the missing
input of Stacks 0FBY and proves for no class other than `0`.

The cap operation of the class of Stacks 0B78 at the test scheme `sT` is, by
`Stacks.Chow.flatPullbackBivariantClass_cap`, the flat pullback along the base change
`pr_T : X ×_S T ⟶ T` of the structure morphism of `X`, and that flat pullback is the exterior
product with `[X]` by
`Stacks.Chow.chowGroupDegreeEquiv_flatPullbackChowSnd_eq_chowExteriorProduct`, which is clause
(1) of Stacks 0B0R. The three conditions of Stacks 0B76 are not proved for the exterior product
here: they are the ones Stacks 0B78 already discharges for the class, and in particular the
compatibility with the Gysin map is inherited from it. -/
theorem isExteriorProductBivariantClass_flatPullbackBivariantClass (C : ChowSituation.{u})
    [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
    (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0) (G : GysinSystem C)
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [Flat sX] [IsIntegral X] (d : ℕ)
    (hfr : AlgebraicGeometry.RelativeDimension sX d)
    (hd : relativeDimension C.dimensionFunction sX (genericPoint X) = (d : ℤ))
    (hfp : FlatPullbackDescends C) (hRG : ProperPushforwardFlatPullbackBaseChange C)
    (h71 : G.FlatPullbackNaturality d) :
    IsExteriorProductBivariantClass C hδ G sX (d : ℤ)
      (fundamentalChowClass C sX (d : ℤ))
      (flatPullbackBivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) d hfr hfp hRG h71) := by
  intro T sT _ k γ
  have hrel := relativeDimension_pullbackSnd sX hfr sT
  have hfac : FlatPullbackFactorsThroughRationalEquivalence C (pullback.fst sX sT ≫ sX)
      (sT ≫ 𝟙 C.S) (pullback.snd sX sT)
      (pullbackSnd_comp_structureMorphism (Category.comp_id sX) sT) d hrel k :=
    hfp (pullback.fst sX sT ≫ sX) (sT ≫ 𝟙 C.S) (pullback.snd sX sT)
      (pullbackSnd_comp_structureMorphism (Category.comp_id sX) sT) d hrel k
  have hfac' : FlatPullbackFactorsThroughRationalEquivalence C (pullback.fst sX sT ≫ sX) sT
      (pullback.snd sX sT) pullback.condition.symm d hrel k :=
    hfp (pullback.fst sX sT ≫ sX) sT (pullback.snd sX sT) pullback.condition.symm d hrel k
  have hcap := (flatPullbackBivariantClass_cap C G sX (𝟙 C.S) sX (Category.comp_id sX) d hfr hfp
      hRG h71 sT k (chowGroupCongr C (Category.comp_id sT).symm k γ)).trans
    (flatPullbackChow_heq_congr_base C rfl (Category.comp_id sT) rfl
      (pullbackSnd_comp_structureMorphism (Category.comp_id sX) sT)
      pullback.condition.symm rfl hrel hrel rfl hfac hfac'
      (chowGroupCongr C (Category.comp_id sT).symm k γ) γ
      (chowGroupCongr_heq C (Category.comp_id sT).symm k γ))
  have hprod := chowGroupDegreeEquiv_flatPullbackChowSnd_eq_chowExteriorProduct C hδ sX sT d
    hrel hd k hfac' γ
  refine ((chowGroupDegreeEquiv_eq_iff_heq C (pullback.fst sX sT ≫ sX)
    (by ring : (d : ℤ) + k = k - -(d : ℤ)) _ _).2 ?_).symm
  exact (hprod ▸ chowGroupDegreeEquiv_heq C (pullback.fst sX sT ≫ sX)
    (add_comm k (d : ℤ)) _).trans hcap.symm

end Stacks.Chow

end
